use std::collections::BTreeMap;

use proc_macro2::Span;
use syn::Error;

use crate::MatchEntry;

pub(crate) fn overlapping_variable(items: &[&MatchEntry]) -> Error {
    // Generate an error message with the appropriate spans
    let mut error = Error::new(Span::call_site(), "No unique fixed bits within group");
    for entry in items {
        error.combine(Error::new(entry.match_span, "Note: in group"));
    }
    error
}

pub(crate) fn overlapping_fixed(items: &[&MatchEntry]) -> Error {
    // Find which cases actually overlap
    let mut cases: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for entry in items {
        cases.entry(entry.match_for_mask(&entry.truncated_mask())).or_default().push(entry);
    }
    let case = cases.values().find(|v| v.len() > 1).expect("expected at least 1 overlapping case");

    // Generate an error message with the appropriate spans
    let mut error = Error::new(
        Span::call_site(),
        format!("{} matches have overlapping fixed bits", case.len()),
    );
    for entry in case {
        error.combine(Error::new(entry.match_span, "Note: overlaps"));
    }

    error
}
