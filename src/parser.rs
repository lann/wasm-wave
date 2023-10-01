//! Web Assembly Value Encoding parser.

use std::{
    borrow::Cow,
    collections::HashSet,
    fmt::Display,
    num::{ParseFloatError, ParseIntError},
    str::FromStr,
};

use indexmap::IndexMap;

use crate::{
    completion::Completions,
    lex::{LexError, Span},
    lex::{Token, Tokenizer},
    ty::WasmTypeKind,
    WasmType, WasmValue,
};

/// A Web Assembly Value Encoding parser.
pub struct Parser<'a> {
    tokens: Tokenizer<'a>,
    peeked: Option<(Token, Span)>,
    completion: bool,
}

pub(crate) const SOME: &str = "some";
pub(crate) const NONE: &str = "none";
pub(crate) const OK: &str = "ok";
pub(crate) const ERR: &str = "err";

impl<'a> Parser<'a> {
    /// Returns a new Parser for the given input.
    pub fn new(input: &'a str) -> Self {
        Self {
            tokens: Tokenizer::new(input),
            peeked: None,
            completion: false,
        }
    }

    /// Enable or disables the completions API, disabled by default. The
    /// completion API is available from [`ParserError::UnexpectedEnd`]
    /// errors returned from parsing.
    pub fn completion(&mut self, enabled: bool) {
        self.completion = enabled;
    }

    /// Parses a WAVE-encoded value of the given [`WasmType`] into a
    /// corresponding [`WasmValue`].
    pub fn parse_value<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        let start = self.pos();
        self.parse_value_inner(ty)
            .map_err(|err| self.handle_unexpected_end_errors(err, start, ty))
    }

    fn parse_value_inner<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        Ok(match ty.kind() {
            WasmTypeKind::Bool => V::make_bool(self.parse_bool()?),
            WasmTypeKind::S8 => V::make_s8(self.parse_number()?),
            WasmTypeKind::S16 => V::make_s16(self.parse_number()?),
            WasmTypeKind::S32 => V::make_s32(self.parse_number()?),
            WasmTypeKind::S64 => V::make_s64(self.parse_number()?),
            WasmTypeKind::U8 => V::make_u8(self.parse_number()?),
            WasmTypeKind::U16 => V::make_u16(self.parse_number()?),
            WasmTypeKind::U32 => V::make_u32(self.parse_number()?),
            WasmTypeKind::U64 => V::make_u64(self.parse_number()?),
            WasmTypeKind::Float32 => V::make_float32(self.parse_number()?),
            WasmTypeKind::Float64 => V::make_float64(self.parse_number()?),
            WasmTypeKind::Char => V::make_char(self.parse_char()?),
            WasmTypeKind::String => V::make_string(self.parse_string()?),
            WasmTypeKind::List => self.parse_list(ty)?,
            WasmTypeKind::Record => self.parse_record(ty)?,
            WasmTypeKind::Tuple => self.parse_tuple(ty)?,
            WasmTypeKind::Variant => self.parse_variant(ty)?,
            WasmTypeKind::Enum => self.parse_enum(ty)?,
            WasmTypeKind::Option => self.parse_option(ty)?,
            WasmTypeKind::Result => self.parse_result(ty)?,
            WasmTypeKind::Flags => self.parse_flags(ty)?,
            WasmTypeKind::Unsupported => {
                return Err(ParserError::Unsupported("unsupported type".into()))
            }
        })
    }

    /// Parses a WAVE-encoded, parenthesized, comma-separated sequence of
    /// values of the given `types`. Any number of option-typed values at
    /// the end of the sequence may be omitted from the input; those will
    /// be returned as `none` values.
    pub fn parse_params<'ty, V: WasmValue + 'static>(
        &mut self,
        types: impl IntoIterator<Item = &'ty V::Type>,
    ) -> Result<Vec<V>, ParserError> {
        self.expect(Token::LParen)?;

        let mut types = types.into_iter();
        let mut values = Vec::with_capacity(types.size_hint().0);
        loop {
            if let Some((Token::RParen, _)) = self.peek_next_non_whitespace()? {
                self.next_non_whitespace()?;
                break;
            }
            let ty = types.next().ok_or_else(|| {
                ParserError::ParseParams(format!(
                    "too many param values; expected {}",
                    values.len()
                ))
            })?;
            values.push(self.parse_value(ty)?);
            if let (Token::RParen, _) = self.expect_any_of(&[Token::Comma, Token::RParen])? {
                break;
            }
        }
        // Handle trailing option types
        for ty in types {
            if ty.kind() == WasmTypeKind::Option {
                let none = V::make_option(ty, None).map_err(ParserError::make_value)?;
                values.push(none);
            } else {
                return Err(ParserError::ParseParams(format!(
                    "not enough param values; got {}",
                    values.len()
                )));
            }
        }
        Ok(values)
    }

    /// Returns the current byte position in the input.
    pub fn pos(&self) -> usize {
        if let Some((_, Span { start, .. })) = self.peeked {
            start
        } else {
            self.tokens.pos()
        }
    }

    fn parse_bool(&mut self) -> Result<bool, ParserError> {
        match self.parse_name()? {
            "false" => Ok(false),
            "true" => Ok(true),
            other => Err(ParserError::unexpected_name(["false", "true"], other)),
        }
    }

    fn parse_number<T>(&mut self) -> Result<T, ParserError>
    where
        T: FromStr,
        ParserError: From<T::Err>,
    {
        let (token, mut span) = self.expect_any_of(&[Token::Dash, Token::Name, Token::Number])?;
        if token == Token::Dash {
            // Whitespace isn't allowed here, so get the next token directly
            match self.tokens.next_token()? {
                Some(Token::Name | Token::Number) => {
                    // Include leading dash in span
                    span.end = self.tokens.pos();
                }
                other => {
                    return Err(ParserError::UnexpectedToken {
                        expected: vec![Token::Name, Token::Number],
                        got: other,
                    })
                }
            }
        }
        Ok(self.tokens.get_span(span).parse()?)
    }

    fn parse_char(&mut self) -> Result<char, ParserError> {
        let span = self.expect(Token::Char)?;
        let inner_span = Span {
            start: span.start + 1,
            end: span.end - 1,
        };
        let len = inner_span.len();
        if len == 0 {
            return Err(ParserError::InvalidChar("empty"));
        }
        let (ch, parsed, _) = self.parse_char_inner(inner_span)?;
        if parsed < len {
            return Err(ParserError::InvalidChar("more than one character"));
        }
        Ok(ch)
    }

    fn parse_string(&mut self) -> Result<Cow<str>, ParserError> {
        let span = self.expect(Token::String)?;
        let start = span.start + 1;
        let end = span.end - 1;

        let mut last_copied = start;
        let mut output = String::new();

        let mut pos = span.start + 1;
        while pos < end {
            let (ch, parsed, is_escape) = self.parse_char_inner(Span { start: pos, end })?;
            if is_escape {
                let chunk = self.tokens.get_span(Span {
                    start: last_copied,
                    end: pos,
                });
                output += chunk;
                output.push(ch);
                last_copied = pos + parsed;
            }
            pos += parsed;
        }
        let last_chunk = self.tokens.get_span(Span {
            start: last_copied,
            end,
        });
        if output.is_empty() {
            // No escapes; we can just return the input span
            Ok(last_chunk.into())
        } else {
            output += last_chunk;
            Ok(output.into())
        }
    }

    fn parse_list<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        self.expect(Token::LSquare)?;

        let mut elements = vec![];
        loop {
            if let Some((Token::RSquare, _)) = self.peek_next_non_whitespace()? {
                break;
            }
            elements.push(self.parse_value(&ty.list_element_type().unwrap())?);
            if let (Token::RSquare, _) = self.expect_any_of(&[Token::Comma, Token::RSquare])? {
                break;
            }
        }
        V::make_list(ty, elements).map_err(ParserError::make_value)
    }

    fn parse_record<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        self.expect(Token::LCurly)?;

        let field_types = ty
            .record_fields()
            .enumerate()
            .map(|(idx, (name, ty))| (name, (idx, ty)))
            .collect::<IndexMap<_, _>>();
        let mut values = vec![None; field_types.len()];
        loop {
            if let Some((Token::RCurly, _)) = self.peek_next_non_whitespace()? {
                break;
            }
            let name = self.parse_name()?;

            let (idx, ty) = field_types
                .get(name)
                .ok_or_else(|| ParserError::RecordFieldUnknown(name.to_string()))?;

            self.expect(Token::Colon)?;

            values[*idx] = Some(self.parse_value(ty)?);

            if let (Token::RCurly, _) = self.expect_any_of(&[Token::Comma, Token::RCurly])? {
                break;
            }
        }
        let fields = field_types
            .iter()
            .zip(values)
            .map(|((name, (_, ty)), maybe_val)| {
                let val = match maybe_val {
                    Some(val) => val,
                    None if ty.kind() == WasmTypeKind::Option => {
                        V::make_option(ty, None).map_err(ParserError::make_value)?
                    }
                    None => return Err(ParserError::RecordFieldMissing(name.to_string())),
                };
                Ok((name.as_ref(), val))
            })
            .collect::<Result<Vec<_>, _>>()?;
        V::make_record(ty, fields).map_err(ParserError::make_value)
    }

    fn parse_tuple<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        self.expect(Token::LParen)?;

        let types = ty.tuple_element_types();
        let mut values = Vec::with_capacity(types.size_hint().0);
        let mut saw_rparen = false;
        for ty in types {
            values.push(self.parse_value(&ty)?);
            if let (Token::RParen, _) = self.expect_any_of(&[Token::Comma, Token::RParen])? {
                saw_rparen = true;
                break;
            }
        }
        if !saw_rparen {
            self.expect(Token::RParen)?;
        }
        V::make_tuple(ty, values).map_err(ParserError::make_value)
    }

    fn parse_variant<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        let name = self.parse_name()?;
        let (case_name, case_ty) = ty
            .variant_cases()
            .find(|(case_name, _)| case_name.as_ref() == name)
            .ok_or_else(|| {
                ParserError::unexpected_name(ty.variant_cases().map(|(name, _)| name), name)
            })?;
        V::make_variant(ty, case_name.as_ref(), self.parse_maybe_payload(case_ty)?)
            .map_err(ParserError::make_value)
    }

    fn parse_enum<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        let name = self.parse_name()?;
        V::make_enum(ty, name).map_err(ParserError::make_value)
    }

    fn parse_option<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        let some_ty = ty.option_some_type().unwrap();
        let peek_name = self.peek_name()?;
        let val = if peek_name.is_some_and(|s| SOME.starts_with(s) || NONE.starts_with(s)) {
            match self.parse_name()? {
                SOME => self.parse_maybe_payload(Some(some_ty))?,
                NONE => None,
                other => {
                    return Err(ParserError::unexpected_name([SOME, NONE], other));
                }
            }
        } else if flattenable(some_ty.kind()) {
            Some(self.parse_value(&some_ty)?)
        } else {
            let got = self.parse_name()?;
            return Err(ParserError::unexpected_name([SOME, NONE], got));
        };
        V::make_option(ty, val).map_err(ParserError::make_value)
    }

    fn parse_result<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        let (ok_ty, err_ty) = ty.result_types().unwrap();
        let peek_name = self.peek_name()?;
        let val = if peek_name.is_some_and(|s| OK.starts_with(s) || ERR.starts_with(s)) {
            match self.parse_name()? {
                OK => Ok(self.parse_maybe_payload(ok_ty)?),
                ERR => Err(self.parse_maybe_payload(err_ty)?),
                other => {
                    return Err(ParserError::unexpected_name([OK, ERR], other));
                }
            }
        } else if ok_ty.is_some() && flattenable(ok_ty.as_ref().unwrap().kind()) {
            Ok(Some(self.parse_value(&ok_ty.unwrap())?))
        } else {
            let got = self.parse_name()?;
            return Err(ParserError::unexpected_name([OK, ERR], got));
        };
        V::make_result(ty, val).map_err(ParserError::make_value)
    }

    fn parse_flags<V: WasmValue>(&mut self, ty: &V::Type) -> Result<V, ParserError> {
        self.expect(Token::LCurly)?;
        let names: HashSet<_> = ty.flags_names().collect();
        let mut flags = vec![];
        loop {
            if let Some((Token::RCurly, _)) = self.peek_next_non_whitespace()? {
                break;
            }
            let name = self.parse_name()?;
            let flag = names
                .get(name)
                .ok_or_else(|| ParserError::unexpected_name(ty.flags_names(), name))?;
            flags.push(flag.as_ref());
            if let (Token::RCurly, _) = self.expect_any_of(&[Token::Comma, Token::RCurly])? {
                break;
            }
        }
        V::make_flags(ty, flags).map_err(ParserError::make_value)
    }

    fn next_non_whitespace(&mut self) -> Result<Option<(Token, Span)>, ParserError> {
        if let Some(peeked) = self.peeked.take() {
            return Ok(Some(peeked));
        }
        for res in &mut self.tokens {
            let (token, span) = res?;
            if token != Token::Whitespace {
                return Ok(Some((token, span)));
            }
        }
        Ok(None)
    }

    fn peek_next_non_whitespace(&mut self) -> Result<Option<(Token, Span)>, ParserError> {
        self.peeked = self.next_non_whitespace()?;
        Ok(self.peeked.clone())
    }

    fn peek_name(&mut self) -> Result<Option<&str>, ParserError> {
        Ok(self
            .peek_next_non_whitespace()?
            .and_then(|(token, span)| (token == Token::Name).then(|| self.tokens.get_span(span))))
    }

    fn expect_any_of(&mut self, expected: &[Token]) -> Result<(Token, Span), ParserError> {
        if let Some((token, span)) = self.next_non_whitespace()? {
            if expected.contains(&token) {
                Ok((token, span))
            } else {
                Err(ParserError::UnexpectedToken {
                    expected: expected.to_vec(),
                    got: Some(token),
                })
            }
        } else {
            Err(ParserError::UnexpectedToken {
                expected: expected.to_vec(),
                got: None,
            })
        }
    }

    fn expect(&mut self, expected: Token) -> Result<Span, ParserError> {
        let (_, span) = self.expect_any_of(&[expected])?;
        Ok(span)
    }

    // Parse a character within a char or string literal. Also returns the
    // number of bytes parsed and whether it was an escape.
    fn parse_char_inner(&self, span: Span) -> Result<(char, usize, bool), ParserError> {
        let span_str = self.tokens.get_span(span);
        let mut chars = span_str.chars();

        let ch = chars.next().unwrap();
        if ch != '\\' {
            return Ok((ch, ch.len_utf8(), false));
        }

        match chars.next().unwrap() {
            esc @ ('\'' | '"' | '\\') => Ok((esc, 2, true)),
            'n' => Ok(('\n', 2, true)),
            'r' => Ok(('\r', 2, true)),
            't' => Ok(('\t', 2, true)),
            'u' => {
                if chars.next() != Some('{') {
                    return Err(ParserError::InvalidEscape(
                        span_str.chars().skip(1).take(2).collect(),
                    ));
                }
                let mut nibbles = chars.clone().map(|ch| ch.to_digit(16));
                let mut num_nibbles = 0;
                let mut value: u32 = 0;
                while let Some(Some(nibble)) = nibbles.next() {
                    num_nibbles += 1;
                    value <<= 4;
                    value |= nibble;
                    if value > 0x10FFFF {
                        return Err(ParserError::InvalidEscape(
                            span_str.chars().skip(1).take(2 + num_nibbles + 1).collect(),
                        ));
                    }
                }
                if chars.nth(num_nibbles) != Some('}') {
                    return Err(ParserError::InvalidEscape(
                        span_str.chars().skip(1).take(2 + num_nibbles + 1).collect(),
                    ));
                }
                match value.try_into() {
                    Ok(ch) => Ok((ch, 3 + num_nibbles + 1, true)),
                    Err(_) => Err(ParserError::InvalidEscape(
                        span_str.chars().skip(1).take(2 + num_nibbles + 1).collect(),
                    )),
                }
            }
            other => Err(ParserError::InvalidEscape(other.to_string())),
        }
    }

    fn parse_name(&mut self) -> Result<&str, ParserError> {
        let span = self.expect(Token::Name)?;
        Ok(self.tokens.get_span(span))
    }

    fn parse_maybe_payload<V: WasmValue>(
        &mut self,
        ty: Option<V::Type>,
    ) -> Result<Option<V>, ParserError> {
        if let Some(ty) = ty {
            self.expect(Token::LParen)?;
            let val = self.parse_value(&ty)?;
            self.expect(Token::RParen)?;
            Ok(Some(val))
        } else {
            Ok(None)
        }
    }

    fn handle_unexpected_end_errors(
        &self,
        err: ParserError,
        start: usize,
        ty: &impl WasmType,
    ) -> ParserError {
        // Convert several errors to `UnexpectedEnd` with optional Completion
        match err {
            ParserError::Lex(LexError::UnexpectedEnd)
            | ParserError::UnexpectedToken { got: None, .. }
            | ParserError::UnexpectedEnd { completions: None } => (),
            ParserError::UnexpectedName { .. } | ParserError::MakeValueError(_)
                if self.tokens.ended() => {}
            _ => return err,
        }
        ParserError::UnexpectedEnd {
            completions: self.completion.then(|| {
                let prefix = self.tokens.get_span(start..);
                crate::completion::Completions::new(ty, prefix)
            }),
        }
    }
}

pub(crate) fn flattenable(kind: WasmTypeKind) -> bool {
    use WasmTypeKind::*;
    !matches!(kind, Variant | Enum | Option | Result)
}

impl<'a> From<Tokenizer<'a>> for Parser<'a> {
    fn from(tokens: Tokenizer<'a>) -> Self {
        Self {
            tokens,
            peeked: None,
            completion: false,
        }
    }
}

impl<'a> From<Parser<'a>> for Tokenizer<'a> {
    fn from(parser: Parser<'a>) -> Self {
        parser.tokens
    }
}

/// A WAVE Parser error.
#[derive(Debug, thiserror::Error)]
pub enum ParserError {
    /// Invalid char encoding
    #[error("invalid char: {0}")]
    InvalidChar(&'static str),
    /// Invalid char or string escape
    #[error("invalid escape: `\\{0}`")]
    InvalidEscape(String),
    /// Invalid `option` or `result` flattening
    #[error("cannot flatten nested {0:?}s")]
    InvalidFlattening(WasmTypeKind),
    /// Lexing (tokenizing) error
    #[error("invalid token: {0}")]
    Lex(#[from] crate::lex::LexError),
    /// Error returned by a [`WasmValue`]`::make_*` method
    #[error("error constructing value: {0}")]
    MakeValueError(String),
    /// Invalid float encoding
    #[error("error parsing float: {0}")]
    ParseFloat(#[from] ParseFloatError),
    /// Invalid integer encoding
    #[error("error parsing int: {0}")]
    ParseInt(#[from] ParseIntError),
    /// Invalid params encoding
    #[error("error parsing params: {0}")]
    ParseParams(String),
    /// Duplicate record field
    #[error("duplicate field `{0}`")]
    RecordFieldDuplicated(String),
    /// Missing record field
    #[error("missing field `{0}`")]
    RecordFieldMissing(String),
    /// Unknown (undefined) record field
    #[error("unknown field `{0}`")]
    RecordFieldUnknown(String),
    /// Unexpected name token
    #[error("expected {expected:?}, got {got:?}")]
    UnexpectedName {
        /// Expected name(s)
        expected: Vec<String>,
        /// Got name
        got: String,
    },
    /// Unexpected end of input
    #[error("unexpected end of input")]
    UnexpectedEnd {
        /// Completion data, if enabled
        completions: Option<Completions>,
    },
    /// Unexpected token type
    #[error("expected {expected:?}, got {got:?}")]
    UnexpectedToken {
        /// Expected token type(s)
        expected: Vec<Token>,
        /// Got token type
        got: Option<Token>,
    },
    /// Unsupported type (e.g. for a particular [`WasmValue`] impl)
    #[error("unsupported type {0}")]
    Unsupported(String),
}

impl ParserError {
    fn make_value(err: impl Display) -> Self {
        Self::MakeValueError(err.to_string())
    }

    fn unexpected_name<I: Into<String>>(
        expected: impl IntoIterator<Item = I>,
        got: impl Into<String>,
    ) -> Self {
        Self::UnexpectedName {
            expected: expected.into_iter().map(Into::into).collect(),
            got: got.into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::value::{Type, Value};

    use super::*;

    #[test]
    fn component_vals_smoke_test() {
        use wasmtime::component::Val;
        for (input, want) in [
            ("false", Val::Bool(false)),
            ("true", Val::Bool(true)),
            ("0", Val::S8(0)),
            ("-1", Val::S16(-1)),
            ("2147483647", Val::S32(2147483647)),
            ("-12345678910", Val::S64(-12345678910)),
            ("255", Val::U8(255)),
            ("65535", Val::U16(65535)),
            ("1", Val::U32(1)),
            ("2", Val::U64(2)),
            ("1.1", Val::Float32(1.1)),
            ("-1.1e+10", Val::Float32(-1.1e+10)),
            ("nan", Val::Float32(f32::NAN)),
            ("inf", Val::Float32(f32::INFINITY)),
            ("-inf", Val::Float32(f32::NEG_INFINITY)),
            ("1.1e-123", Val::Float64(1.1e-123)),
            ("nan", Val::Float64(f64::NAN)),
            ("inf", Val::Float64(f64::INFINITY)),
            ("-inf", Val::Float64(f64::NEG_INFINITY)),
            ("'x'", Val::Char('x')),
            ("'☃'", Val::Char('☃')),
            (r"'\\'", Val::Char('\\')),
            (r"'\''", Val::Char('\'')),
            (r"'\n'", Val::Char('\n')),
            (r"'\u{0}'", Val::Char('\0')),
            (r"'\u{1b}'", Val::Char('\x1b')),
            (r"'\u{7F}'", Val::Char('\x7f')),
            (r"'\u{10ffff}'", Val::Char('\u{10ffff}')),
            (r#""abc""#, Val::String("abc".into())),
            (r#""☃\\\"\n""#, Val::String("☃\\\"\n".into())),
            (r#""\u{0}\u{7f}""#, Val::String("\x00\x7F".into())),
        ] {
            assert_eq!(parse_unwrap::<Val>(input, want.ty()), want);
        }
    }

    #[test]
    fn core_vals_smoke_test() {
        use wasmtime::{Val, ValType};

        assert_eq!(parse_unwrap::<Val>("10", ValType::I32).unwrap_i32(), 10);
        assert_eq!(parse_unwrap::<Val>("-10", ValType::I64).unwrap_i64(), -10);
        assert_eq!(parse_unwrap::<Val>("1.5", ValType::F32).unwrap_f32(), 1.5);
        assert_eq!(parse_unwrap::<Val>("-1.5", ValType::F64).unwrap_f64(), -1.5);
        assert_eq!(
            parse_unwrap::<Val>("(1234605616436508552,1311768467294899695)", ValType::V128)
                .unwrap_v128(),
            0x1234567890abcdef1122334455667788
        );
    }

    #[test]
    fn parse_bare_option_or_result() {
        let ty = Type::option(Type::BOOL);
        assert_eq!(
            parse_value("true", &ty),
            Value::make_option(&ty, Some(Value::Bool(true))).unwrap()
        );
        let ty = Type::result(Some(Type::BOOL), None);
        assert_eq!(
            parse_value("false", &ty),
            Value::make_result(&ty, Ok(Some(Value::Bool(false)))).unwrap()
        );
    }

    #[test]
    fn parse_params_empty() {
        let vals: Vec<Value> = Parser::new("()").parse_params([]).unwrap();
        assert!(vals.is_empty());
    }

    #[test]
    fn parse_params_tests() {
        for (types, input, expected) in [
            (vec![Type::BOOL], "(true)", "(true)"),
            (
                vec![Type::U8, Type::option(Type::U8), Type::option(Type::U8)],
                "(1)",
                "(1, none, none)",
            ),
            (
                vec![Type::U8, Type::option(Type::U8), Type::option(Type::U8)],
                "(1, 2)",
                "(1, some(2), none)",
            ),
            (
                vec![Type::U8, Type::option(Type::U8), Type::option(Type::U8)],
                "(1, 2, 3)",
                "(1, some(2), some(3))",
            ),
        ] {
            let vals: Vec<Value> = Parser::new(input)
                .parse_params(&types)
                .unwrap_or_else(|err| panic!("error decoding params {input:?}: {err}"));
            let tuple = Type::tuple(types).unwrap();
            let tuple_str = crate::to_string(&Value::make_tuple(&tuple, vals).unwrap()).unwrap();
            assert_eq!(tuple_str, expected, "for {input:?}");
        }
    }

    fn parse_unwrap<V: WasmValue>(input: &str, ty: V::Type) -> V {
        Parser::new(input)
            .parse_value(&ty)
            .unwrap_or_else(|err| panic!("error decoding {input:?}: {err}"))
    }

    fn parse_value(input: &str, ty: &Type) -> Value {
        Parser::new(input)
            .parse_value(ty)
            .unwrap_or_else(|err| panic!("error decoding {input:?}: {err}"))
    }
}
