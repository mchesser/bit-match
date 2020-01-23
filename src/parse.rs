use std::collections::HashMap;

use syn::parse::{Parse, ParseStream};
use syn::{punctuated::Punctuated, Expr, Ident, LitInt, Result, Token};

use crate::helpers::bits_to_string;

mod kw {
    syn::custom_keyword!(read);
    syn::custom_keyword!(var);
    syn::custom_keyword!(pattern);
}

/// The fully parsed bit match input
#[derive(Debug, Default)]
pub struct BitMatchInput {
    pub readers: Vec<BitReader>,
    pub matches: Vec<MatchEntry>,
}

impl Parse for BitMatchInput {
    fn parse(mut input: ParseStream) -> Result<Self> {
        let mut readers = vec![];
        let mut matches = vec![];

        let mut symbol_table = SymbolTable::default();

        while !input.is_empty() {
            let lookahead = input.lookahead1();
            if lookahead.peek(kw::read) {
                readers.push(input.parse()?)
            }
            else if lookahead.peek(Token![const]) {
                symbol_table.parse_const(&mut input)?;
            }
            else if lookahead.peek(kw::var) {
                symbol_table.parse_var(&mut input)?;
            }
            else if lookahead.peek(kw::pattern) {
                symbol_table.parse_pattern_def(&mut input)?;
            }
            else {
                matches.push(MatchEntry::parse(&mut input, &symbol_table)?);
                parse_optional_comma(&mut input);
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

fn parse_optional_comma(input: &mut ParseStream) {
    if input.peek(Token![,]) {
        input.parse::<Token![,]>().unwrap();
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

#[derive(Clone, Default)]
struct SymbolTable {
    values: HashMap<String, SymbolValue>,
    patterns: HashMap<String, PatternDef>,
}

impl SymbolTable {
    /// Parse a statement of the form: `const <ident> = <bit string>;
    fn parse_const(&mut self, input: &mut ParseStream) -> Result<()> {
        input.parse::<Token![const]>()?;
        let name = input.parse::<Ident>()?.to_string();
        input.parse::<Token![=]>()?;

        let mut pattern = vec![];
        while !input.peek(Token![;]) {
            pattern.extend(parse_fixed_bits(input, true)?);
        }
        input.parse::<Token![;]>()?;

        self.values.insert(name, SymbolValue::Const(pattern));
        Ok(())
    }

    /// Parse a statement of the form: `var <ident> = <num-bits>;
    fn parse_var(&mut self, input: &mut ParseStream) -> Result<()> {
        input.parse::<kw::var>()?;
        let name = input.parse::<Ident>()?.to_string();
        input.parse::<Token![:]>()?;
        let num_bits = input.parse::<LitInt>()?.base10_parse()?;
        input.parse::<Token![;]>()?;

        self.values.insert(name.clone(), SymbolValue::Var(name, Metadata::new(num_bits)));
        Ok(())
    }

    /// Parse a statement of the form: `pattern <ident>(<args..>) => (<token stream>)`
    fn parse_pattern_def(&mut self, input: &mut ParseStream) -> Result<()> {
        input.parse::<kw::pattern>()?;
        let name = input.parse::<Ident>()?.to_string();

        // Parse pattern args
        let content;
        syn::parenthesized!(content in input);
        let args: Punctuated<Ident, Token![,]> = content.parse_terminated(Ident::parse)?;
        let args = args.into_iter().collect();

        input.parse::<Token![=>]>()?;

        // Parse pattern body
        let content;
        syn::parenthesized!(content in input);
        let body = content.parse()?;

        input.parse::<Token![;]>()?;

        self.patterns.insert(name, PatternDef { args, body });
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum SymbolValue {
    Const(Vec<bool>),
    Var(String, Metadata),
    Indirect(String, Option<Metadata>),
    Multiple(Vec<SymbolValue>),
}

#[derive(Debug, Clone)]
struct PatternDef {
    args: Vec<Ident>,
    body: proc_macro2::TokenStream,
}

/// A pattern component representing variable bits
#[derive(Debug)]
pub struct Variable {
    /// The name of the identifier that will be assigned to this variable
    pub name: String,

    /// The collection of bit-slices that are used to construct the variable
    pub bits: Vec<BitSlice>,
}

impl Variable {
    /// Computes the total number of bits required to store this variable
    ///
    /// Used for computing the output type of the variable
    pub fn total_bits(&self) -> usize {
        self.bits.iter().map(|bits| bits.length + bits.shift).max().unwrap_or(0)
    }
}

/// Represents a contiguous slice of bits within a bit stream
#[derive(Debug, Copy, Clone)]
pub struct BitSlice {
    /// The offset of slice within the input bit stream
    pub offset: usize,

    /// The number of bits that should
    pub length: usize,

    /// The amount this value should be shifted
    pub shift: usize,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MaskState {
    Fixed,
    Variable,
    Any,
}

/// Represents a fully parsed match arm
pub struct MatchEntry {
    /// Tracks which bits are fixed (mask[i] == true) and which are variable (mask[i] == false)
    pub mask: Vec<bool>,

    /// The values of the fixed bits to match against
    pub fixed: Vec<bool>,

    /// Metadata for describing the position of variable bits within the bit stream
    pub variable: Vec<Variable>,

    /// Keeps track of fixed bits that we don't care about the value of (used for default cases)
    pub any_mask: Vec<bool>,

    /// The body of the match expression
    pub body: Expr,

    /// The span for the match part of the entry
    pub match_span: proc_macro2::Span,
}

impl std::fmt::Debug for MatchEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MatchEntry { ")?;
        write!(f, "mask: {}, ", bits_to_string(&self.mask))?;
        write!(f, "fixed: {}, ", bits_to_string(&self.fixed))?;
        write!(f, "variable: {:?}, ", self.variable)?;
        write!(f, "any_mask: {}, ", bits_to_string(&self.any_mask))?;
        write!(f, "body: () }}")?;
        Ok(())
    }
}

impl MatchEntry {
    pub fn debug_string(&self) -> String {
        let mut output = String::new();
        for ((&mask_bit, &fixed_bit), &any_bit) in
            self.mask.iter().zip(self.fixed.iter()).zip(self.any_mask.iter())
        {
            if !mask_bit {
                output.push('x');
            }
            else if any_bit {
                output.push('_');
            }
            else if fixed_bit {
                output.push('1');
            }
            else {
                output.push('0');
            }
        }
        output
    }

    pub fn mask_iter<'a>(&'a self) -> impl Iterator<Item = MaskState> + 'a {
        self.mask.iter().zip(&self.any_mask).map(|x| match x {
            (true, true) => MaskState::Any,
            (true, false) => MaskState::Fixed,
            _ => MaskState::Variable,
        })
    }

    pub fn current_mask(&self, used_bits: &[bool]) -> Vec<bool> {
        let fixed_bits: Vec<_> = match self.has_fixed_bits(&used_bits) {
            true => self.mask_iter().map(|x| x == MaskState::Fixed).collect(),
            false => self.mask_iter().map(|x| x == MaskState::Any).collect(),
        };

        let mut unused_bits = crate::bit_not(&used_bits);
        unused_bits.resize(fixed_bits.len(), true);
        crate::bit_and(&fixed_bits, &unused_bits)
    }

    pub fn matches(&self, key: &[bool], mask: &[bool]) -> bool {
        for i in 0..mask.len() {
            if mask[i] && !(key[i] == self.fixed[i] || self.any_mask[i]) {
                return false;
            }
        }
        true
    }

    /// Checks whether the are any remaining fixed bits
    pub fn has_fixed_bits(&self, used_bits: &[bool]) -> bool {
        for (bit, is_used) in
            self.mask_iter().zip(used_bits.iter().chain(std::iter::repeat(&false)))
        {
            if !is_used && bit == MaskState::Fixed {
                return true;
            }
        }
        false
    }

    /// Checks whether there are `any` bits for a particular mask
    pub fn has_any_bits(&self, mask: &[bool]) -> bool {
        for (&mask_bit, &any_bit) in mask.iter().zip(self.any_mask.iter()) {
            if mask_bit && any_bit {
                return true;
            }
        }
        false
    }

    /// Extract all `fixed` bits for a given mask
    pub fn fixed_bits(&self, mask: &[bool]) -> Vec<bool> {
        crate::bit_and(&self.fixed, mask)
    }
}

impl MatchEntry {
    fn parse(input: &mut ParseStream, symbols: &SymbolTable) -> Result<Self> {
        let pattern_group: PatternGroup = input.parse()?;
        let match_span = pattern_group.span.clone();

        let resolved_group = {
            let mut resolver = ResolvedPatternGroup::default();
            resolver.resolve(pattern_group, symbols).map_err(|e| input.error(e))?;
            resolver
        };

        let mut mask = vec![false; resolved_group.total_bits];
        let mut fixed = vec![false; resolved_group.total_bits];
        let mut any_mask = vec![false; resolved_group.total_bits];

        // For each fixed bit slice in this group update the mask and fixed bit values
        for entry in resolved_group.fixed {
            mask[entry.range()].iter_mut().for_each(|bit| *bit = true);
            fixed[entry.range()].copy_from_slice(&entry.bits);
        }

        // Iterate through each set of variable bits, grouping them by name. This is done in reverse
        // order to allow the shift amount to be computed correctly for auto variables.
        let mut variable: Vec<Variable> = vec![];
        for entry in resolved_group.variable.into_iter().rev() {
            if entry.name == "_" {
                mask[entry.range()].iter_mut().for_each(|bit| *bit = true);
                any_mask[entry.range()].iter_mut().for_each(|bit| *bit = true);
                continue;
            }

            let var = match variable.iter_mut().find(|e| e.name == entry.name) {
                Some(entry) => entry,
                None => {
                    variable.push(Variable { name: entry.name, bits: vec![] });
                    variable.last_mut().unwrap()
                }
            };

            let shift = entry.shift.unwrap_or(var.total_bits());
            var.bits.push(BitSlice { offset: entry.offset, length: entry.length, shift });
        }

        input.parse::<Token![=>]>()?;
        let body = input.parse()?;

        Ok(Self { mask, fixed, variable, any_mask, body, match_span })
    }
}

struct FixedBits {
    offset: usize,
    bits: Vec<bool>,
}

impl FixedBits {
    fn range(&self) -> std::ops::Range<usize> {
        self.offset..self.offset + self.bits.len()
    }
}

struct VariableBits {
    name: String,
    offset: usize,
    length: usize,
    shift: Option<usize>,
}

impl VariableBits {
    fn range(&self) -> std::ops::Range<usize> {
        self.offset..self.offset + self.length
    }
}

#[derive(Default)]
struct ResolvedPatternGroup {
    fixed: Vec<FixedBits>,
    variable: Vec<VariableBits>,
    total_bits: usize,
}

impl ResolvedPatternGroup {
    fn add_fixed(&mut self, bits: Vec<bool>) {
        let num_bits = bits.len();
        self.fixed.push(FixedBits { offset: self.total_bits, bits });
        self.total_bits += num_bits;
    }

    fn add_variable(&mut self, name: String, meta: Metadata) {
        self.variable.push(VariableBits {
            name: name.into(),
            offset: self.total_bits,
            length: meta.length,
            shift: meta.shift,
        });
        self.total_bits += meta.length;
    }

    fn resolve(
        &mut self,
        group: PatternGroup,
        symbols: &SymbolTable,
    ) -> std::result::Result<(), String> {
        for component in group.components {
            match component {
                Component::Fixed(bits) => self.add_fixed(bits),
                Component::Symbol(name, meta) => self.resolve_symbol(name, meta, symbols)?,
                Component::Pattern(name, params) => self.expand_pattern(name, params, symbols)?,
            }
        }
        Ok(())
    }

    fn resolve_symbol_value(
        &mut self,
        value: &SymbolValue,
        meta: Option<Metadata>,
        symbols: &SymbolTable,
    ) -> std::result::Result<(), String> {
        match value {
            SymbolValue::Const(bits) => self.add_fixed(bits.clone()),
            SymbolValue::Var(name, base) => self.add_variable(name.clone(), base.merge(meta)?),
            SymbolValue::Indirect(name, base) => {
                let meta = match base {
                    Some(base) => Some(base.merge(meta)?),
                    None => meta,
                };
                self.resolve_symbol(name.clone(), meta, symbols)?;
            }
            SymbolValue::Multiple(values) => {
                for value in values {
                    self.resolve_symbol_value(value, meta, symbols)?;
                }
            }
        }

        Ok(())
    }

    fn resolve_symbol(
        &mut self,
        name: String,
        meta: Option<Metadata>,
        symbols: &SymbolTable,
    ) -> std::result::Result<(), String> {
        if let Some(symbol) = symbols.values.get(&name) {
            return self.resolve_symbol_value(symbol, meta, symbols);
        }

        // If there is no global symbol defined for this name, then this could be a locally
        // defined single letter variable, where the length is defined based on the number
        // of characters in the name
        let auto_name = auto_var_name(&name)?;

        // Check for shadowing in an existing symbol
        if symbols.values.contains_key(&auto_name) {
            return Err(format!("`{}` already defined", auto_name));
        }

        self.add_variable(auto_name, Metadata::new(name.len()));
        Ok(())
    }

    fn expand_pattern(
        &mut self,
        name: String,
        params: Vec<PatternGroup>,
        symbols: &SymbolTable,
    ) -> std::result::Result<(), String> {
        let pattern =
            symbols.patterns.get(&name).ok_or_else(|| format!("pattern not found: `{}`", name))?;

        let mut pattern_symbols = symbols.clone();
        for (ident, entry) in pattern.args.iter().zip(params) {
            let mut inner_symbols = vec![];
            for value in entry.components {
                inner_symbols.push(match value {
                    Component::Fixed(bits) => SymbolValue::Const(bits),
                    Component::Symbol(name, meta) => SymbolValue::Indirect(name, meta),
                    Component::Pattern(_, _) => {
                        return Err("pattern call must not appear inside of ".into())
                    }
                });
            }

            pattern_symbols.values.insert(ident.to_string(), SymbolValue::Multiple(inner_symbols));
        }

        // Now resolve the inner body
        let inner_body: PatternGroup =
            syn::parse2(pattern.body.clone()).map_err(|e| e.to_string())?;
        self.resolve(inner_body, &pattern_symbols)
    }
}

#[derive(Debug)]
struct PatternGroup {
    components: Vec<Component>,
    span: proc_macro2::Span,
}

impl Parse for PatternGroup {
    /// Parses the 'pattern' part of the next match arm
    fn parse(input: ParseStream) -> Result<Self> {
        let mut span = input.cursor().span();
        let mut components = vec![];

        while !input.is_empty() {
            let lookahead = input.lookahead1();

            if !(lookahead.peek(Ident) || lookahead.peek(LitInt)) {
                if components.is_empty() {
                    return Err(lookahead.error());
                }
                break;
            }

            // Update the input span to cover the sub-component
            if let Some(joint_span) = span.join(input.cursor().span()) {
                span = joint_span;
            }

            components.push(Component::parse(input)?);
        }

        Ok(Self { components, span })
    }
}

#[derive(Debug)]
enum Component {
    Fixed(Vec<bool>),
    Symbol(String, Option<Metadata>),
    Pattern(String, Vec<PatternGroup>),
}

impl Parse for Component {
    fn parse(mut input: ParseStream) -> Result<Self> {
        if input.peek(Ident) {
            let name = input.parse::<Ident>()?.to_string();
            if !input.peek(syn::token::Paren) {
                let metadata = match input.peek(syn::token::Bracket) {
                    true => Some(input.parse()?),
                    false => None,
                };
                return Ok(Self::Symbol(name.to_string(), metadata));
            }

            let content;
            syn::parenthesized!(content in input);
            let params: Punctuated<PatternGroup, Token![,]> =
                content.parse_terminated(PatternGroup::parse)?;

            Ok(Self::Pattern(name, params.into_iter().collect()))
        }
        else if input.peek(LitInt) {
            Ok(Self::Fixed(parse_fixed_bits(&mut input, false)?))
        }
        else {
            Err(input.error(
                "Invalid input, expected a known symbol, fixed bits (e.g. `00110`), or variable\
                bits (e.g. `aaaa`) declaration",
            ))
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct Metadata {
    length: usize,
    shift: Option<usize>,
}

impl Metadata {
    fn new(length: usize) -> Metadata {
        Metadata { length, shift: None }
    }

    fn merge(self, other: Option<Metadata>) -> std::result::Result<Metadata, String> {
        let other = match other {
            Some(other) => other,
            None => return Ok(self),
        };

        let self_shift = self.shift.unwrap_or(0);
        let other_shift = other.shift.unwrap_or(0);

        if self_shift + self.length < self_shift + other_shift + other.length {
            return Err("Variable index out of bounds".into());
        }
        Ok(Metadata { shift: Some(self_shift + other_shift), length: other.length })
    }
}

impl Parse for Metadata {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let _ = syn::bracketed!(content in input);

        let high = content.parse::<LitInt>()?.base10_parse()?;
        let low = match content.peek(Token![:]) {
            true => {
                content.parse::<Token![:]>()?;
                content.parse::<LitInt>()?.base10_parse()?
            }
            false => high,
        };

        if low > high {
            return Err(input.error("High bit must be greater than low bit"));
        }

        Ok(Metadata { shift: Some(low), length: high - low + 1 })
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
            '_' => (),
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
