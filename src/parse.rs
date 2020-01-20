use std::{collections::HashMap, iter};

use syn::parse::{Parse, ParseStream};
use syn::{Expr, Ident, LitInt, Result, Token};

mod kw {
    syn::custom_keyword!(read);
    syn::custom_keyword!(var);
    syn::custom_keyword!(pattern);
}

/// The fully parsed bit match input
#[derive(Debug)]
pub struct BitMatchInput {
    pub readers: Vec<BitReader>,
    pub matches: Vec<MatchEntry>,
}

impl Parse for BitMatchInput {
    fn parse(mut input: ParseStream) -> Result<Self> {
        let mut readers = vec![];
        let mut matches = vec![];

        let mut symbol_table = HashMap::new();

        while !input.is_empty() {
            let lookahead = input.lookahead1();
            if lookahead.peek(kw::read) {
                readers.push(input.parse()?)
            }
            else if lookahead.peek(Token![const]) {
                let symbol = Symbol::parse_const(&mut input)?;
                symbol_table.insert(symbol.name, symbol.value);
            }
            else if lookahead.peek(kw::var) {
                let symbol = Symbol::parse_var(&mut input)?;
                symbol_table.insert(symbol.name, symbol.value);
            }
            else if lookahead.peek(kw::pattern) {
                panic!("`pattern` expressions are not currently supported");
            }
            else {
                matches.push(MatchEntry::parse(&mut input, &symbol_table)?);

                // Parse optional `,` token after each entry
                let lookahead = input.lookahead1();
                if lookahead.peek(Token![,]) {
                    input.parse::<Token![,]>()?;
                }
            }
        }

        // The matcher will never be able to make progress if there is no way to read values, so
        // report an error to the user if there is no defined read expression
        if readers.is_empty() {
            return Err(input.error("Expected at least 1 reader expression"));
        }

        Ok(Self { readers, matches })
    }
}

/// A statement of the form: `read <num_bits> => <expr>;`
#[derive(Debug)]
pub struct BitReader {
    pub num_bits: usize,
    pub expr: Expr,
}

impl Parse for BitReader {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<kw::read>()?;
        let num_bits = input.parse::<LitInt>()?.base10_parse()?;
        input.parse::<Token![=>]>()?;
        let expr = input.parse::<Expr>()?;
        input.parse::<Token![;]>()?;

        Ok(Self { num_bits, expr })
    }
}

#[derive(Debug)]
enum SymbolValue {
    Const(Vec<bool>),
    Var(usize),
}

#[derive(Debug)]
struct Symbol {
    name: String,
    value: SymbolValue,
}

impl Symbol {
    // Parse statement of the form: `const <ident> = <bit string>;
    fn parse_const(input: &mut ParseStream) -> Result<Self> {
        input.parse::<Token![const]>()?;
        let name = input.parse::<Ident>()?.to_string();
        input.parse::<Token![=]>()?;
        let pattern = parse_fixed_bits(input, true)?;
        input.parse::<Token![;]>()?;

        Ok(Self { name, value: SymbolValue::Const(pattern) })
    }

    // Parse statement of the form: `var <ident> = <num-bits>;
    fn parse_var(input: &mut ParseStream) -> Result<Self> {
        input.parse::<kw::var>()?;
        let name = input.parse::<Ident>()?.to_string();
        input.parse::<Token![=]>()?;
        let num_bits = input.parse::<LitInt>()?.base10_parse()?;
        input.parse::<Token![;]>()?;

        Ok(Self { name, value: SymbolValue::Var(num_bits) })
    }
}

/// A pattern component representing variable bits
#[derive(Debug)]
pub struct Variable {
    pub name: String,
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

impl MatchEntry {
    fn parse(input: &mut ParseStream, symbols: &HashMap<String, SymbolValue>) -> Result<Self> {
        let match_entry = parse_pattern_components(input, symbols)?;

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
fn parse_pattern_components(
    input: &mut ParseStream,
    symbols: &HashMap<String, SymbolValue>,
) -> Result<PatternComponents> {
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

        components.push(FixedOrVariable::parse(input, symbols)?);
    }

    Ok(PatternComponents { components, span })
}

#[derive(Debug)]
pub enum FixedOrVariable {
    /// Represents a set bits that are expected to be fixed (e.g. `0010`)
    Fixed(Vec<bool>),

    /// Represents a set of bits by name and bit count that are expected to vary
    Variable((String, usize)),
}

impl FixedOrVariable {
    fn parse(input: &mut ParseStream, symbols: &HashMap<String, SymbolValue>) -> Result<Self> {
        if input.peek(Ident) {
            let prev = input.fork();
            let name = input.parse::<Ident>()?.to_string();

            // Check whether this identifier exists in the symbol table
            match symbols.get(&name) {
                Some(SymbolValue::Const(bits)) => Ok(Self::Fixed(bits.clone())),

                Some(SymbolValue::Var(size)) => Ok(Self::Variable((name, *size))),

                None => {
                    // Otherwise this is interpreted as a locally defined single letter variable
                    let size = name.len();
                    match auto_var_name(&name) {
                        Ok(name) if symbols.contains_key(&name) => {
                            Err(prev.error(format!("{} already defined globally", name)))
                        }
                        Ok(name) => Ok(Self::Variable((name, size))),
                        Err(e) => Err(prev.error(e)),
                    }
                }
            }
        }
        else if input.peek(LitInt) {
            Ok(Self::Fixed(parse_fixed_bits(input, false)?))
        }
        else {
            Err(input.error(
                "Invalid input, expected a known symbol, fixed bits (e.g. `00110`), or variable\
                bits (e.g. `aaaa`) declaration",
            ))
        }
    }
}

// Converts an integer literal to a string, then computes a bit vector based on the `0` and `1` in
// the string
fn parse_fixed_bits(input: &mut ParseStream, global: bool) -> Result<Vec<bool>> {
    let value: LitInt = input.parse()?;

    let mut bits = vec![];
    for bit in value.to_string().chars() {
        match bit {
            '0' => bits.push(false),
            '1' => bits.push(true),
            'a'..='z' | 'A'..='Z' if !global => {
                return Err(input.error(
                    "Fixed bits must be either `0` or `1`\n\
                    Note: spaces are required between fixed and variable bits",
                ));
            }
            _ => return Err(input.error("Fixed bits must be either `0` or `1`")),
        }
    }

    Ok(bits)
}

fn auto_var_name(value: &String) -> std::result::Result<String, &'static str> {
    let name = value.chars().next().unwrap();

    // Check that all characters are the same
    for char_ in value.chars() {
        if char_ != name {
            return Err("Auto vars must only contain a single letter");
        }
    }

    Ok(format!("{}", name))
}
