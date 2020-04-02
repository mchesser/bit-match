use proc_macro2::Span;
use syn::Error;

use crate::{
    helpers::{bits_to_string, group_by},
    MatchEntry,
};

pub fn overlapping_fixed(items: &[&MatchEntry], used_bits: &[bool]) -> Error {
    // Group entries by fixed bits so we can determine which entries actually overlap
    let groups = group_by(items.iter().map(|x| *x), |entry| entry.fixed_bits(used_bits));

    let overlapping =
        groups.values().find(|v| v.len() > 1).map(|x| x.as_slice()).unwrap_or_else(|| {
            eprintln!("Internal error: matches reported as overlapping, but are actually unique.");
            items
        });

    let overlap_mask = bits_to_string(&crate::bit_not(used_bits));

    let mut error = Error::new(
        Span::call_site(),
        format!("{} matches overlap when mask is {}", overlapping.len(), overlap_mask),
    );
    for entry in overlapping {
        error.combine(Error::new(
            entry.match_span,
            format!("Match is {} here:", entry.debug_string()),
        ));
    }

    error
}
