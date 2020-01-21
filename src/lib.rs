extern crate proc_macro;

mod errors;
mod gen;
mod parse;

use std::collections::BTreeMap;

use syn::{parse_macro_input, Result};

use crate::{gen::DecoderState, parse::*};

#[proc_macro]
pub fn match_bits(tokens: self::proc_macro::TokenStream) -> self::proc_macro::TokenStream {
    let input = parse_macro_input!(tokens as BitMatchInput);

    let matches_ref: Vec<_> = input.matches.iter().collect();
    let match_tree = match MatchTree::new(&matches_ref) {
        Ok(tree) => tree,
        Err(e) => return e.to_compile_error().into(),
    };

    DecoderState::new(&input.readers).build_token_stream(&match_tree).into()
}

type MatchBranchArm<'a> = (Vec<bool>, MatchTree<'a>);

#[derive(Debug)]
enum MatchTree<'a> {
    Branch { mask: Vec<bool>, arms: Vec<MatchBranchArm<'a>> },
    Leaf(&'a MatchEntry),
}

impl<'a> MatchTree<'a> {
    pub(crate) fn new(input: &[&'a MatchEntry]) -> Result<Self> {
        let mut tree = MatchTree::build(input)?;
        tree.verify_and_optimize(vec![])?;
        Ok(tree)
    }

    fn empty() -> MatchTree<'a> {
        Self::Branch { mask: vec![], arms: vec![] }
    }

    fn build(input: &[&'a MatchEntry]) -> Result<Self> {
        assert!(!input.is_empty(), "Attempted to build match tree with no inputs");

        // Group entries by their fixed bit mask
        let mut groups: BTreeMap<&[bool], Vec<&MatchEntry>> = BTreeMap::new();
        for entry in input {
            groups.entry(entry.truncated_mask()).or_default().push(entry);
        }

        // If there is only one mask group, then leaf nodes follow the current matches
        if groups.len() == 1 {
            let (mask, entries) = groups.into_iter().next().unwrap();
            let arms = entries
                .into_iter()
                .map(|entry| (entry.match_for_mask(mask), Self::Leaf(entry)))
                .collect();
            return Ok(MatchTree::Branch { mask: mask.into(), arms });
        };

        // Find fixed bits that are shared between all masks in this group
        let mut shared_mask = vec![true; groups.keys().map(|k| k.len()).min().unwrap()];
        for mask in groups.keys() {
            shared_mask = crate::bit_and(&shared_mask, mask);
        }

        // Remove trailing zeros from shared mask, this prevents reading bits that are just going to
        // be zeroed when applying the mask
        while shared_mask.last() == Some(&false) {
            shared_mask.pop();
        }

        // Generate match groups based on the fixed bits in the mask
        let mut sub_matches: BTreeMap<Vec<bool>, Vec<&MatchEntry>> = BTreeMap::new();
        for entry in input {
            let match_for_entry = entry.match_for_mask(&shared_mask);
            sub_matches.entry(match_for_entry).or_default().push(entry);
        }

        if sub_matches.len() == 1 {
            // We failed to make progress -- meaning there are no unique fixed bits within this
            // sub-branch
            return Err(errors::overlapping_variable(&groups));
        }

        // Recursively create subtrees for each branch
        let mut arms = vec![];
        for (key, entries) in sub_matches {
            arms.push((key, MatchTree::build(&entries)?));
        }

        Ok(MatchTree::Branch { mask: shared_mask, arms })
    }

    /// Optimize the match statements at each level of the tree, by avoiding masking against bits
    fn verify_and_optimize(&mut self, matched_bits: Vec<bool>) -> Result<()> {
        if let MatchTree::Branch { mask, arms } = self {
            let mut new_matched_bits = matched_bits.clone();
            new_matched_bits.resize(matched_bits.len().max(mask.len()), false);

            // Zero out bits from the current mask that have already been matched, and keep
            // track of bits that are newly matched in this subtree.
            for (current, all) in mask.iter_mut().zip(new_matched_bits.iter_mut()) {
                if *all {
                    *current = false;
                }
                else if *current {
                    *all = true
                }
            }

            // Calculate how many new bits will be matched in this sub-branch
            let bits_to_match: usize = mask.iter().filter(|b| **b).count();

            if arms.len() > (1 << bits_to_match) {
                // If there are more arms then there are possible combinations of bits, then there
                // must be at least 1 overlapping bit.
                return Err(errors::overlapping_fixed(&self.entries()));
            }

            // If all bits in this branch has been fully matched then this branch is already
            // covered by previous matches, so it can be safely flattened
            if bits_to_match == 0 {
                *self = std::mem::replace(&mut arms[0].1, Self::empty());
                return Ok(());
            }

            // Verify and flatten sub-branches
            for (match_value, branch) in arms.iter_mut() {
                *match_value = crate::bit_and(match_value, &mask);
                branch.verify_and_optimize(new_matched_bits.clone())?;
            }
        }

        Ok(())
    }

    /// Returns all leaf nodes (i.e. match entries) within this tree
    fn entries(&self) -> Vec<&'a MatchEntry> {
        match self {
            Self::Branch { arms, .. } => arms.iter().flat_map(|(_, a)| a.entries()).collect(),
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
