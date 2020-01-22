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

use crate::{gen::DecoderState, helpers::bits_to_string, parse::*};

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
    fn new(key: Vec<bool>, entries: &[&'a MatchEntry], used_bits: Vec<bool>) -> Result<Self> {
        Ok(match entries {
            [entry] => Self { key, sub_tree: MatchTree::Leaf(entry) },
            _ => Self { key, sub_tree: MatchTree::build(entries, used_bits)? },
        })
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

fn shared_mask<'a>(entries: &[&'a MatchEntry]) -> Vec<bool> {
    if entries.is_empty() {
        return vec![];
    }

    let mut mask: Vec<_> = entries[0].mask_iter().collect();
    for entry in entries.iter().skip(1) {
        mask = mask.into_iter().zip(entry.mask_iter()).map(|(a, b)| a.and(b)).collect();
    }

    let mut fixed_mask: Vec<_> =
        mask.into_iter().map(|x| x == crate::parse::MaskState::Fixed).collect();
    while fixed_mask.last() == Some(&false) {
        fixed_mask.pop();
    }
    fixed_mask
}

impl<'a> MatchTree<'a> {
    pub(crate) fn new(input: &[&'a MatchEntry]) -> Result<Self> {
        MatchTree::build(input, vec![])
    }

    fn build(input: &[&'a MatchEntry], mut used_bits: Vec<bool>) -> Result<Self> {
        assert!(!input.is_empty(), "Attempted to build match tree with no inputs");

        // Find fixed bits that are shared between all groups
        let mut mask: Vec<_> = shared_mask(input);
        update_used_bits(&mut used_bits, &mut mask);


        if !mask.contains(&true) {
            // No remaining fixed bits
            if input.len() == 1 {
                return Ok(MatchTree::Leaf(input[0]));
            }
            return Err(errors::overlapping_fixed(input));
        }

        // Generate match groups based on the fixed bits in the mask
        let mut all_any = vec![];
        let mut partial_any = vec![];
        let mut sub_matches: BTreeMap<Vec<bool>, Vec<&MatchEntry>> = BTreeMap::new();
        for entry in input {
            if entry.all_any(&mask) {
                all_any.push(*entry);
                continue;
            }

            if entry.is_fixed(&mask) {
                let match_for_entry = entry.fixed_bits(&mask);
                sub_matches.entry(match_for_entry).or_default().push(entry);
            }
            else {
                partial_any.push(*entry);
            }
        }

        let any_sub_tree = match !all_any.is_empty() {
            true => Some(Box::new(MatchTree::build(&all_any, used_bits.clone())?)),
            false => None,
        };

        // Create subtrees for each branch with fixed bits
        let mut arms = vec![];
        for (key, mut entries) in sub_matches {
            // Add any remaining entries with 'any' bits if the fixed bits match
            for entry in &partial_any {
                if entry.matches(&key, &mask) {
                    entries.push(*entry);
                }
            }
            arms.push(MatchBranchArm::new(key, &entries, used_bits.clone())?)
        }

        Ok(MatchTree::Branch { mask, arms, any_sub_tree })
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
