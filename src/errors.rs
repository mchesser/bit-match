use std::collections::BTreeMap;

use proc_macro2::Span;
use syn::Error;

use crate::{
    helpers::{bits_to_string, group_by},
    MatchEntry,
};

pub fn overlapping_variable(groups: &BTreeMap<&[bool], Vec<&MatchEntry>>) -> Error {
    let mut error = Error::new(Span::call_site(), format!("No unique fixed bits within group"));
    for (key, entries) in groups {
        let msg = format!("Note: mask = {} ({})", bits_to_string(key), key.len());
        for entry in entries {
            error.combine(Error::new(entry.match_span, msg.clone()));
        }
    }
    error
}

pub fn overlapping_fixed(items: &[&MatchEntry]) -> Error {
    // Group entries by fixed bits so we can determine which entries actually overlap
    let groups = group_by(items, |entry| entry.fixed_bits(&entry.truncated_mask()));
    let overlapping = groups
        .values()
        .find(|v| v.len() > 1)
        .expect("Internal error: matches reported as overlapping, but are actually unique.");

    let mut error = Error::new(
        Span::call_site(),
        format!("{} matches have overlapping fixed bits", overlapping.len()),
    );
    for entry in overlapping {
        error.combine(Error::new(
            entry.match_span,
            format!("Note: value is {}", entry.debug_string()),
        ));
    }

    error
}
