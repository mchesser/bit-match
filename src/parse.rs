use std::iter;

use syn::parse::{Parse, ParseStream};
use syn::{Expr, Ident, LitInt, Result, Token};

mod kw {
    syn::custom_keyword!(read);
}

/// The fully parsed bit match input
#[derive(Debug)]
pub struct BitMatchInput {
    pub readers: Vec<(usize, Expr)>,
    pub matches: Vec<MatchEntry>,
}

impl Parse for BitMatchInput {
    fn parse(input: ParseStream) -> Result<Self> {
        // Parse one or more 'read' statements of the form: `read <num_bits> => <expr>;`
        let mut readers = vec![];
        loop {
            let lookahead = input.lookahead1();
            if !lookahead.peek(kw::read) {
                break;
            }

            input.parse::<kw::read>()?;
            let num_bits = input.parse::<LitInt>()?.base10_parse()?;
            input.parse::<Token![=>]>()?;
            let expr = input.parse::<Expr>()?;
            input.parse::<Token![;]>()?;

            readers.push((num_bits, expr));
        }

        if readers.is_empty() {
            return Err(input.error("Expected at least 1 reader expression"));
        }

        // Parse all match arms
        let mut matches = vec![];
        while !input.is_empty() {
            matches.push(input.parse()?);

            // Parse optional `,` token after each entry
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(Self { readers, matches })
    }
}

/// A pattern component representing variable bits
#[derive(Debug)]
pub struct Variable {
    pub name: char,
    pub bits: Vec<(usize, usize)>,
}


/// Represents a fully parsed match arm
#[derive(Debug)]
pub struct MatchEntry {
    /// A mask for all fixed bits
    pub mask: Vec<bool>,

    /// Keeps track of all bits that have a fixed value
    pub fixed: Vec<bool>,

    /// Keeps track of all bits that vary
    pub variable: Vec<Variable>,

    /// The body of the match expression
    pub body: Expr,

    /// The span for the match part of the entry
    pub match_span: proc_macro2::Span,
}

impl MatchEntry {
    /// Truncates the mask of this entry to the position of the final fixed bit.
    ///
    /// This is used to ensure that variable length instructions with the same fixed bits are mapped
    /// to the same mask.
    pub fn truncated_mask(&self) -> &[bool] {
        let last_fixed_bit = self.mask.iter().rposition(|&p| p).unwrap_or(0);
        &self.mask[..=last_fixed_bit]
    }

    /// Given a mask output output all matched fixed bits
    pub fn match_for_mask(&self, mask: &[bool]) -> Vec<bool> {
        crate::bit_and(&self.fixed, mask)
    }
}

impl Parse for MatchEntry {
    fn parse(input: ParseStream) -> Result<Self> {
        let match_entry = input.call(parse_pattern_components)?;

        let mut mask = vec![];
        let mut fixed = vec![];
        let mut variable: Vec<Variable> = vec![];

        // Extract the individual pattern components, and compute the final fixed-bit mask
        for item in match_entry.components {
            match item {
                FixedOrVariable::Fixed(bits) => {
                    mask.extend(iter::repeat(true).take(bits.len()));
                    fixed.extend_from_slice(&bits);
                }

                FixedOrVariable::Variable((name, len)) => {
                    let var = match variable.iter_mut().find(|e| e.name == name) {
                        Some(entry) => entry,
                        None => {
                            variable.push(Variable { name, bits: vec![] });
                            variable.last_mut().unwrap()
                        }
                    };
                    var.bits.push((mask.len(), len));

                    mask.extend(iter::repeat(false).take(len));
                    fixed.extend(iter::repeat(false).take(len));
                }
            }
        }

        let body = input.parse()?;

        Ok(Self { mask, fixed, variable, body, match_span: match_entry.span })
    }
}

struct PatternComponents {
    components: Vec<FixedOrVariable>,
    span: proc_macro2::Span,
}

/// Parses the 'pattern' part of the next match arm
fn parse_pattern_components(input: ParseStream) -> Result<PatternComponents> {
    let mut span = input.cursor().span();
    let mut components = vec![];

    loop {
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![=>]) {
            // We have reached the end of the pattern
            input.parse::<Token![=>]>()?;
            break;
        }

        if !(lookahead.peek(Ident) || lookahead.peek(LitInt)) {
            return Err(lookahead.error());
        }

        // Update the input span to cover the sub-component
        if let Some(joint_span) = span.join(input.cursor().span()) {
            span = joint_span;
        }

        components.push(input.parse()?);
    }

    Ok(PatternComponents { components, span })
}

#[derive(Debug)]
pub enum FixedOrVariable {
    /// Represents a set bits that are expected to be fixed (e.g. `0010`)
    Fixed(Vec<bool>),

    /// Represents a set of bits by name and bit count that are expected to vary
    Variable((char, usize)),
}

impl Parse for FixedOrVariable {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Ident) {
            let prev = input.fork();
            let ident: Ident = input.parse()?;

            let value = ident.to_string();
            let name = value.chars().next().unwrap();

            // Check that all characters are the same
            for char_ in value.chars() {
                if char_ != name {
                    return Err(prev.error("Spaces are required between variable bits"));
                }
            }

            Ok(Self::Variable((name, value.len())))
        }
        else if input.peek(LitInt) {
            let prev = input.fork();
            let lit: LitInt = input.parse()?;

            // Convert the literal to a string so that we can extract the individual bits from the
            // number
            let mut bits = vec![];
            for bit in lit.to_string().chars() {
                match bit {
                    '0' => bits.push(false),
                    '1' => bits.push(true),
                    'a'..='z' | 'A'..='Z' => {
                        let mut error = prev.error("Fixed bits must be either `0` or `1`");
                        error.combine(
                            prev.error("Note: spaces are required between fixed and variable bits"),
                        );
                        return Err(error);
                    }
                    _ => return Err(prev.error("Fixed bits must be either `0` or `1`")),
                }
            }

            Ok(Self::Fixed(bits))
        }
        else {
            Err(input.error(
                "Invalid input, expected fixed bits (e.g. `00110`) or variable bits  (e.g. `aaaa`) \
                 declaration",
            ))
        }
    }
}
