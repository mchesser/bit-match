use std::cmp::Ordering;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{parse_quote, Expr, Ident, LitInt, Stmt, Type};

use crate::{
    helpers::{bits_to_string, first_bit, get_mask},
    BitMatchInput, BitReader, MatchBranchArm, MatchEntry, MatchTree,
};

#[derive(Clone)]
pub(crate) struct DecoderState<'a> {
    /// Contains the length (in bits) and the identifier for values that have already been read at
    /// a previous subtree level
    subtree_values: Vec<(usize, Ident)>,

    /// Stores expressions that can be used to retrieve bytes from some source.
    read_exprs: &'a [BitReader],

    any_case_cover: usize,
    used_bits: Vec<bool>,
    values: Vec<bool>,
}

impl<'a> DecoderState<'a> {
    pub fn new(input: &'a BitMatchInput) -> Self {
        Self {
            subtree_values: vec![],
            read_exprs: &input.readers,
            used_bits: vec![],
            values: vec![],
            any_case_cover: 0,
        }
    }

    pub fn build_token_stream(self, tree: &MatchTree) -> TokenStream {
        match tree {
            MatchTree::Branch { mask, arms, default_case } => {
                decode_branch(self, mask, &arms, default_case)
            }
            MatchTree::Leaf(entry) => decode_leaf(self, entry),
        }
    }

    /// Returns the total number of bits we have read from the decoder so far
    fn total_decoded_bits(&self) -> usize {
        self.subtree_values.iter().map(|(len, _)| len).sum()
    }

    /// Generates an expression value and any read statements required to get all bits in the value
    fn read_and_get(&mut self, mask: &[bool]) -> (Vec<Stmt>, Expr) {
        let mut read_stmts = vec![];
        while let Some(stmt) = self.read_next(mask.len()) {
            read_stmts.push(stmt);
        }

        (read_stmts, self.try_get_value(mask).expect("Failed to generate match expression"))
    }

    /// Generates an expression that reads a value given the target mask. Returns `None` if
    /// insufficent bytes have been read from the decoder.
    ///
    /// Note: The bits in `mask` must be contiguous.
    fn try_get_value(&self, mask: &[bool]) -> Option<Expr> {
        let decoded_bits = self.total_decoded_bits();
        if decoded_bits < mask.len() {
            return None;
        }

        let mut partial_values = vec![];
        let mut used_bits = mask.len() as isize - decoded_bits as isize;

        let top_fixed_bit = first_bit(mask);
        let required_bits = mask.len() - top_fixed_bit;

        let mask_ty = bits_lit_type(required_bits);
        let mask_lit = bits_to_literal(&mask[top_fixed_bit..]);

        for (len, ident) in self.subtree_values.iter().rev() {
            let shift_amount = used_bits;
            used_bits += *len as isize;

            if used_bits > 0 {
                partial_values.push(shift(parse_quote!(#ident), &mask_ty, shift_amount));
            }

            if used_bits >= required_bits as isize {
                break;
            }
        }

        Some(parse_quote!(((#(#partial_values)|*) & #mask_lit)))
    }

    /// Generates a statement that reads additional bits from the underlying reader.
    ///
    /// This method will attempt to generate a the smallest single statement that reads the smallest
    /// number of bits required for us to have read `required_bits`. If it is not possible to do so
    /// in a single statement, then the largest possible read will be generated, and this method
    /// should be called again.
    ///
    /// Returns `None` if we have already read `required_bits`.
    fn read_next(&mut self, required_bits: usize) -> Option<Stmt> {
        let new_bits = required_bits.checked_sub(self.total_decoded_bits())?;
        if new_bits == 0 {
            return None;
        }

        // Generate a unique identifier for this value
        let next_ident =
            Ident::new(&format!("__x{}", self.subtree_values.len()), Span::call_site());

        // Get the smallest possible read expression
        let last = || self.read_exprs.last().expect("At least 1 read expression is required");
        let BitReader { num_bits: len, expr: read_expr } =
            self.read_exprs.iter().find(|r| r.num_bits >= new_bits).unwrap_or_else(last);

        self.subtree_values.push((*len, next_ident.clone()));
        Some(parse_quote!(let #next_ident = #read_expr;))
    }

    fn debug_string(&self, mask: &[bool]) -> String {
        let len = mask.len().max(self.used_bits.len()).max(self.values.len());
        let mut output = String::with_capacity(len);

        for i in 0..len {
            let mask_bit = *mask.get(i).unwrap_or(&false);
            let used_bit = *self.used_bits.get(i).unwrap_or(&false);
            let value = *self.values.get(i).unwrap_or(&false);

            if used_bit {
                output.push(if value { '1' } else { '0' });
            }
            else {
                output.push(if mask_bit { '?' } else { '_' });
            }
        }

        output
    }
}

fn decode_branch(
    mut state: DecoderState,
    mask: &[bool],
    arms: &[MatchBranchArm],
    default_case: &Option<Box<MatchTree>>,
) -> TokenStream {
    let (read_stmts, match_expr) = state.read_and_get(mask);

    // For each branch, decode the inner subtree and generate a match arm
    let arm_tokens: Vec<_> = arms
        .iter()
        .map(|arm| {
            let mut new_state = state.clone();
            new_state.used_bits.resize(state.used_bits.len().max(mask.len()), false);
            new_state.values.resize(state.used_bits.len().max(mask.len()), false);
            for i in 0..mask.len() {
                if mask[i] {
                    new_state.used_bits[i] = true;
                    new_state.values[i] = arm.key[i];
                }
            }

            let debug_string = new_state.debug_string(&[]);
            let arm_lit = bits_to_literal(&arm.key[first_bit(mask)..]);
            let inner_tokens = new_state.build_token_stream(&arm.sub_tree);
            quote!(
                #[doc(#debug_string)]
                #arm_lit => { #inner_tokens }
            )
        })
        .collect();

    let expected_arms = 1 << crate::count_ones(mask);
    let covered_cases = arms.len() + state.any_case_cover;
    let catch_all = match covered_cases.cmp(&expected_arms) {
        Ordering::Less => match default_case {
            // The default case is covered by a default arm provided by the user
            Some(default_case) => {
                let mut new_state = state.clone();
                new_state.any_case_cover = arms.len();
                new_state.build_token_stream(&*default_case)
            }

            None => {
                let error = format!(
                    "{} out of {} cases not covered for: {}",
                    expected_arms - covered_cases,
                    expected_arms,
                    state.debug_string(mask),
                );

                if expected_arms < 128 {
                    let extended_error = find_missing_cases(mask, arms, &state);
                    let error = format!(
                        "{}\nnote: the following cases where not covered:\n{}",
                        error, extended_error
                    );
                    quote!(compile_error!(#error))
                }
                else {
                    quote!(compile_error!(#error))
                }
            }
        },

        // All cases are covered, however the compiler doesn't know this, so generate an
        // unreachable expression (this should be optimized away)
        Ordering::Equal => quote!(unreachable!()),

        // This should have already been checked during the construction of the tree
        Ordering::Greater => unreachable!("Generated a match statement with too many arms"),
    };

    quote! {
        #(#read_stmts)*

        match #match_expr {
            #(#arm_tokens,)*
            _ => { #catch_all }
        }
    }
}

fn find_missing_cases(mask: &[bool], arms: &[MatchBranchArm], state: &DecoderState) -> String {
    let count = 1 << crate::count_ones(mask);
    let mut set: std::collections::BTreeSet<Vec<_>> = std::collections::BTreeSet::new();
    for i in 0..count {
        let mut value = Vec::with_capacity(mask.len());
        let mut bits = i;
        for &mask_bit in mask.iter().rev() {
            if mask_bit {
                value.push(if bits & 1 == 0 { false } else { true });
                bits = bits >> 1;
            }
            else {
                value.push(false);
            }
        }
        set.insert(value.into_iter().rev().collect());
    }

    for arm in arms {
        set.remove(&arm.key);
    }

    let mut output = Vec::with_capacity(set.len());
    for entry in set {
        let mut tmp_state = state.clone();
        tmp_state.used_bits.resize(tmp_state.used_bits.len().max(mask.len()), false);
        tmp_state.values.resize(tmp_state.used_bits.len().max(mask.len()), false);
        for i in 0..mask.len() {
            if mask[i] {
                tmp_state.used_bits[i] = true;
                tmp_state.values[i] = entry[i];
            }
        }
        output.push(format!("\t{}", tmp_state.debug_string(&[])));
    }

    format!("{}", output.join("\n"))
}

fn decode_leaf(mut state: DecoderState, entry: &MatchEntry) -> TokenStream {
    // Check that all fixed bits have been covered at this node
    if entry.has_fixed_bits(&state.used_bits) {
        let error = format!("Not all cases covered for: {}", state.debug_string(&entry.mask));
        return quote!(compile_error!(#error));
    }

    // Variable bits may occur in data that we have yet to read, so we keep track of new the
    // read statements we need to perform here.
    let mut read_stmts: Vec<Stmt> = vec![];

    // For each set of variable bits, we create a new statement that defines a local
    // identifier assigned to the extracted value.
    let mut variable_stmts: Vec<Stmt> = vec![];
    for var in &entry.variable {
        let ident = Ident::new(&format!("{}", var.name), Span::call_site());
        let ty = bits_lit_type(var.total_bits());

        // Each variable might consist of multiple sets of not contiguous bits, so here
        // extract each of the variable components, cast them to the correct size and shift
        // them to the appropriate position.
        // (this is common when encoding instructions that contain immediate values).
        let mut values: Vec<Expr> = vec![];
        for slice in &var.bits {
            let (reads, value) = state.read_and_get(&get_mask(slice.offset, slice.length));
            read_stmts.extend_from_slice(&reads);
            values.push(shift(parse_quote!(#value), &ty, slice.shift as isize));
        }

        variable_stmts.push(parse_quote!(let #ident = #(#values)|*;))
    }

    let body = &entry.body;
    quote! {
        #(#read_stmts)*
        #(#variable_stmts)*
        #body
    }
}

/// Gets the smallest possible integer type for the specified number of bits
fn bits_lit_type(num_bits: usize) -> Type {
    match num_bits {
        0..=8 => parse_quote!(u8),
        9..=16 => parse_quote!(u16),
        16..=32 => parse_quote!(u32),
        32..=64 => parse_quote!(u64),
        64..=128 => parse_quote!(u128),
        _ => panic!("Maximum match size is 128-bits"),
    }
}

/// Converts a collection of bits to the smallest possible fixed sized integer literal
fn bits_to_literal(bits: &[bool]) -> LitInt {
    LitInt::new(&format!("0b{}", bits_to_string(bits)), Span::call_site())
}

/// Shift an expression by a positive (left) or negative (right) amount.
fn shift(expr: Expr, out_type: &Type, amount: isize) -> Expr {
    if amount < 0 {
        let shift = LitInt::new(&format!("{}", -amount), Span::call_site());
        parse_quote!((#expr >> #shift) as #out_type)
    }
    else if amount > 0 {
        let shift = LitInt::new(&format!("{}", amount), Span::call_site());
        parse_quote!(((#expr as #out_type) << #shift))
    }
    else {
        parse_quote!(#expr as #out_type)
    }
}
