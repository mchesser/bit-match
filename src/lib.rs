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
    fn new(
        key: Vec<bool>,
        entries: &[&'a MatchEntry],
        used_bits: Vec<bool>,
        depth: usize,
    ) -> Result<Self> {
        Ok(match entries {
            [entry] => Self { key, sub_tree: MatchTree::Leaf(entry) },
            _ => Self { key, sub_tree: MatchTree::build(entries, used_bits, depth)? },
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

fn shared_mask<'a>(entries: &[&'a MatchEntry], used_bits: &[bool]) -> Vec<bool> {
    if entries.is_empty() {
        return vec![];
    }

    let mut mask: Vec<_> = entries[0].current_mask(used_bits);
    for entry in entries {
        let entry_mask = entry.current_mask(used_bits);
        if crate::DEBUG {
            eprintln!("Mask for: {} is: {}", entry.debug_string(), bits_to_string(&entry_mask));
        }
        mask = mask.into_iter().zip(entry_mask).map(|(a, b)| a & b).collect();
    }

    while mask.last() == Some(&false) {
        mask.pop();
    }
    mask
}

impl<'a> MatchTree<'a> {
    pub(crate) fn new(input: &[&'a MatchEntry]) -> Result<Self> {
        MatchTree::build(input, vec![], 0)
    }

    fn build(input: &[&'a MatchEntry], mut used_bits: Vec<bool>, depth: usize) -> Result<Self> {
        assert!(!input.is_empty(), "Attempted to build match tree with no inputs");

        // Find fixed bits that are shared between all groups
        let mut mask: Vec<_> = shared_mask(input, &used_bits);
        update_used_bits(&mut used_bits, &mut mask);

        // Check if there are any remaining shared fixed bits to use
        if !mask.contains(&true) {
            if input.len() == 1 {
                return Ok(MatchTree::Leaf(input[0]));
            }

            // Discard any cases that entirely overlap with the current input
            let fixed_inputs: Vec<_> =
                input.iter().copied().filter(|x| !x.has_any_bits(&used_bits)).collect();

            match fixed_inputs.len() {
                0 => return Err(errors::overlapping_fixed(&input, &used_bits)),
                1 => return MatchTree::build(&fixed_inputs, used_bits, depth + 1),
                _ => return Err(errors::overlapping_fixed(&fixed_inputs, &used_bits)),
            }
        }

        // Generate match groups based on the fixed bits in the mask
        let mut all_any = vec![];
        let mut sub_matches: BTreeMap<Vec<bool>, Vec<&MatchEntry>> = BTreeMap::new();
        for entry in input {
            if entry.has_any_bits(&mask) {
                all_any.push(*entry);
            }
            else {
                let match_for_entry = entry.fixed_bits(&mask);
                sub_matches.entry(match_for_entry).or_default().push(entry);
            }
        }

        let any_sub_tree = match !all_any.is_empty() {
            true => Some(Box::new(MatchTree::build(&all_any, used_bits.clone(), depth + 1)?)),
            false => None,
        };

        // Create subtrees for each branch with fixed bits
        let mut arms = vec![];
        for (key, mut entries) in sub_matches {
            for entry in &all_any {
                if entry.matches(&key, &mask) {
                    entries.push(*entry);
                }
            }
            arms.push(MatchBranchArm::new(key, &entries, used_bits.clone(), depth + 1)?)
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

fn bit_not(a: &[bool]) -> Vec<bool> {
    a.iter().map(|x| !*x).collect()
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
