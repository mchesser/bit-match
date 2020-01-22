extern crate proc_macro;

mod errors;
mod gen;
mod helpers;
mod parse;

use std::collections::BTreeMap;

use syn::{parse_macro_input, Result};

#[cfg(feature = "internal-debug")]
const DEBUG: bool = true;

#[cfg(not(feature = "internal-debug"))]
const DEBUG: bool = false;

use crate::{
    gen::DecoderState,
    helpers::{bits_to_string, group_by},
    parse::*,
};

#[proc_macro]
pub fn match_bits(tokens: self::proc_macro::TokenStream) -> self::proc_macro::TokenStream {
    let input = parse_macro_input!(tokens as BitMatchInput);

    let matches_ref: Vec<_> = input.matches.iter().collect();

    if DEBUG {
        let matches = format!("const a: b = {:#?};", matches_ref);
        std::fs::write("matches.rs", matches.as_bytes()).unwrap();
    }

    let match_tree = match MatchTree::new(&matches_ref) {
        Ok(tree) => tree,
        Err(e) => return e.to_compile_error().into(),
    };

    if DEBUG {
        let debug_tree = format!("const a: b = {:#?};", match_tree);
        std::fs::write("tree.rs", debug_tree.as_bytes()).unwrap();
    }

    DecoderState::new(&input).build_token_stream(&match_tree).into()
}

struct MatchBranchArm<'a> {
    key: Vec<bool>,
    sub_tree: MatchTree<'a>,
}

impl<'a> std::fmt::Debug for MatchBranchArm<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MatchBranchArm { ")?;
        write!(f, "key: \"{}\", ", bits_to_string(&self.key))?;
        write!(f, "sub_tree: {:?} }}", self.sub_tree)?;
        Ok(())
    }
}

impl<'a> MatchBranchArm<'a> {
    fn leaf(entry: &'a MatchEntry, mask: &[bool]) -> Self {
        Self { key: entry.fixed_bits(mask), sub_tree: MatchTree::Leaf(entry) }
    }

    fn sub_tree(key: Vec<bool>, entries: &[&'a MatchEntry]) -> Result<Self> {
        Ok(Self { key, sub_tree: MatchTree::build(entries, vec![])? })
    }
}

enum MatchTree<'a> {
    Branch {
        mask: Vec<bool>,
        arms: Vec<MatchBranchArm<'a>>,
        any_sub_tree: Option<Box<MatchTree<'a>>>,
    },
    Leaf(&'a MatchEntry),
}

impl<'a> std::fmt::Debug for MatchTree<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Branch { mask, arms, any_sub_tree } => {
                f.write_str("Branch {")?;
                write!(f, "mask: \"{}\", ", bits_to_string(mask))?;
                write!(f, "arms: {:?}, ", arms)?;
                write!(f, "any_sub_tree: {:?} }}", any_sub_tree)?;
            }
            Self::Leaf(entry) => write!(f, "Leaf ( {:?} )", entry)?,
        }
        Ok(())
    }
}

fn update_used_bits(used_bits: &mut Vec<bool>, mask: &mut [bool]) {
    used_bits.resize(used_bits.len().max(mask.len()), false);

    // Zero out bits from the current mask that have already been matched, and keep
    // track of bits that are newly matched in this subtree.
    for (current, all) in mask.iter_mut().zip(used_bits.iter_mut()) {
        if *all {
            *current = false;
        }
        else if *current {
            *all = true
        }
    }
}

fn shared_mask<'a>(masks: impl IntoIterator<Item = &'a [bool]> + 'a) -> Vec<bool> {
    let mut shared_mask: Option<Vec<bool>> = None;
    for mask in masks {
        shared_mask = Some(match shared_mask.take() {
            Some(shared_mask) => bit_and(&shared_mask, &mask),
            None => mask.to_vec(),
        });
    }

    let mut shared_mask = shared_mask.unwrap_or(vec![]);
    while shared_mask.last() == Some(&false) {
        shared_mask.pop();
    }

    shared_mask
}

impl<'a> MatchTree<'a> {
    pub(crate) fn new(input: &[&'a MatchEntry]) -> Result<Self> {
        let mut tree = MatchTree::build(input, vec![])?;
        tree.verify_and_optimize(vec![])?;
        Ok(tree)
    }

    fn empty() -> MatchTree<'a> {
        Self::Branch { mask: vec![], arms: vec![], any_sub_tree: None }
    }

    fn build(input: &[&'a MatchEntry], mut used_bits: Vec<bool>) -> Result<Self> {
        assert!(!input.is_empty(), "Attempted to build match tree with no inputs");

        // Group entries by their fixed bit mask
        let groups = group_by(input.iter().map(|x| *x), |entry| entry.truncated_mask());

        // If there is only one mask group, then leaf nodes follow the current matches
        if groups.len() == 1 {
            let (mask, entries) = groups.into_iter().next().unwrap();
            let mut mask = mask.to_vec();
            update_used_bits(&mut used_bits, &mut mask);

            let mut any_arms = vec![];
            let mut arms = vec![];

            for entry in entries {
                if !entry.is_fixed(&mask) {
                    any_arms.push(entry);
                    continue;
                }
                arms.push(MatchBranchArm::leaf(entry, &mask));
            }

            let any_sub_tree = match any_arms.len() {
                0 => None,
                1 => Some(Box::new(MatchTree::Leaf(&any_arms[0]))),
                _ => {
                    let mut used_bits = vec![];
                    let mut shared_mask = shared_mask(any_arms.iter().map(|x| &*x.any_mask));
                    update_used_bits(&mut used_bits, &mut shared_mask);
                    Some(Box::new(MatchTree::build(&any_arms, used_bits)?))
                }
            };

            return Ok(MatchTree::Branch { mask: mask.into(), arms, any_sub_tree });
        }

        // Find fixed bits that are shared between all groups
        let mut shared_mask = shared_mask(groups.keys().map(|x| *x));
        update_used_bits(&mut used_bits, &mut shared_mask);

        // Generate match groups based on the fixed bits in the mask
        let mut any_matches = vec![];
        let mut sub_matches: BTreeMap<Vec<bool>, Vec<&MatchEntry>> = BTreeMap::new();
        for entry in input {
            if !entry.is_fixed(&shared_mask) {
                any_matches.push(*entry);
                continue;
            }
            let match_for_entry = entry.fixed_bits(&shared_mask);
            sub_matches.entry(match_for_entry).or_default().push(entry);
        }

        if sub_matches.len() == 1 {
            // We failed to make progress -- meaning there are no unique fixed bits within this
            // sub-branch
            return Err(errors::overlapping_variable(&groups));
        }

        // Create subtrees for all `any` matches that have no fixed bits for this mask
        let mut any_arms = vec![];
        any_matches.retain(|entry| {
            if entry.all_any(&shared_mask) {
                any_arms.push(*entry);
                return false;
            }
            true
        });

        let any_sub_tree = match !any_arms.is_empty() {
            true => Some(Box::new(MatchTree::build(&any_arms, used_bits)?)),
            false => None,
        };

        // Create subtrees for each branch with fixed bits
        let mut arms = vec![];
        for (key, mut entries) in sub_matches {
            // Add any remaining entries with 'any' bits if the fixed bits match
            for entry in &any_matches {
                if entry.matches(&key, &shared_mask) {
                    entries.push(*entry);
                }
            }
            arms.push(MatchBranchArm::sub_tree(key, &entries)?);
        }

        Ok(MatchTree::Branch { mask: shared_mask, arms, any_sub_tree })
    }

    /// Optimize the match statements at each level of the tree, by avoiding masking against bits
    fn verify_and_optimize(&mut self, mut used_bits: Vec<bool>) -> Result<()> {
        if let MatchTree::Branch { mask, arms, any_sub_tree } = self {
            // Verify and flattern any arm
            if let Some(sub_tree) = any_sub_tree {
                sub_tree.verify_and_optimize(used_bits.clone())?;
            }

            update_used_bits(&mut used_bits, mask);

            // Calculate how many new bits will be matched in this sub-branch
            let bits_to_match: usize = mask.iter().filter(|b| **b).count();
            let combinations = 1 << bits_to_match;

            // Determine whether there are any overlapping branches, by checking that the number of
            // fixed branches is less than the number of possible combinations of bits
            if arms.iter().count() > combinations {
                return Err(errors::overlapping_fixed(&self.entries()));
            }

            // If all bits in this branch has been fully matched then this branch is already
            // covered by previous matches, so it can be safely flattened
            if bits_to_match == 0 {
                if arms.len() == 1 {
                    *self = std::mem::replace(&mut arms[0].sub_tree, Self::empty());
                    return Ok(());
                }

                if let Some(any_sub_tree) = any_sub_tree.take() {
                    assert!(arms.is_empty());
                    *self = *any_sub_tree;
                    return Ok(());
                }
            }

            // Verify and flatten sub-branches
            for arm in arms {
                arm.key = crate::bit_and(&arm.key, &mask);
                arm.sub_tree.verify_and_optimize(used_bits.clone())?;
            }
        }

        Ok(())
    }

    /// Returns all leaf nodes (i.e. match entries) within this tree
    fn entries(&self) -> Vec<&'a MatchEntry> {
        match self {
            Self::Branch { arms, .. } => arms.iter().flat_map(|a| a.sub_tree.entries()).collect(),
            Self::Leaf(leaf) => vec![leaf],
        }
    }
}

/// Performs a bit-wise 'and' operation between two inputs. If the inputs are of different length,
/// the result will be trancated to the size of the smallest input
fn bit_and(a: &[bool], b: &[bool]) -> Vec<bool> {
    let mut a: Vec<_> = a.into();

    a.truncate(b.len());
    for (self_bit, &mask_bit) in a.iter_mut().zip(b) {
        if !mask_bit {
            *self_bit = false;
        }
    }

    a
}

/// Count the number of 'ones' (i.e. true values) in a boolean array.
fn count_ones(bits: impl AsRef<[bool]>) -> usize {
    bits.as_ref().iter().filter(|s| **s).count()
}

trait FromBits {
    fn from_bits(bits: &[bool]) -> Self;
}

macro_rules! impl_from_bits {
    ($target_type: ty) => {
        impl FromBits for $target_type {
            fn from_bits(bits: &[bool]) -> Self {
                let mut acc: $target_type = 0;
                for &bit in bits.iter() {
                    acc = (acc << 1) + (if bit { 1 } else { 0 })
                }
                acc
            }
        }
    };
}

impl_from_bits!(u8);
impl_from_bits!(u16);
impl_from_bits!(u32);
impl_from_bits!(u64);
impl_from_bits!(u128);
