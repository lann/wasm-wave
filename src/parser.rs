use std::{
    borrow::Cow,
    collections::HashMap,
    fmt::Display,
    num::{ParseFloatError, ParseIntError},
    str::FromStr,
};

use crate::{
    lex::Span,
    lex::{Token, Tokenizer},
    ty::Kind,
    Type, Val,
};

pub struct Parser<'a> {
    tokens: Tokenizer<'a>,
    peeked: Option<(Token, Span)>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            tokens: Tokenizer::new(input),
            peeked: None,
        }
    }

    pub fn parse_value<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        Ok(match ty.kind() {
            Kind::Bool => V::make_bool(self.parse_bool()?),
            Kind::S8 => V::make_s8(self.parse_number()?),
            Kind::S16 => V::make_s16(self.parse_number()?),
            Kind::S32 => V::make_s32(self.parse_number()?),
            Kind::S64 => V::make_s64(self.parse_number()?),
            Kind::U8 => V::make_u8(self.parse_number()?),
            Kind::U16 => V::make_u16(self.parse_number()?),
            Kind::U32 => V::make_u32(self.parse_number()?),
            Kind::U64 => V::make_u64(self.parse_number()?),
            Kind::Float32 => V::make_float32(self.parse_number()?),
            Kind::Float64 => V::make_float64(self.parse_number()?),
            Kind::Char => V::make_char(self.parse_char()?),
            Kind::String => V::make_string(self.parse_string()?),
            Kind::List => self.parse_list(ty)?,
            Kind::Record => self.parse_record(ty)?,
            Kind::Tuple => self.parse_tuple(ty)?,
            Kind::Variant => self.parse_variant(ty)?,
            Kind::Enum => self.parse_enum(ty)?,
            Kind::Option => self.parse_option(ty)?,
            Kind::Result => self.parse_result(ty)?,
            Kind::Flags => self.parse_flags(ty)?,
            Kind::Unsupported => return Err(Error::Unsupported(format!("{ty:?}"))),
        })
    }

    fn parse_bool(&mut self) -> Result<bool, Error> {
        match self.parse_name()? {
            "false" => Ok(false),
            "true" => Ok(true),
            other => Err(Error::UnexpectedName {
                expected: vec!["false".into(), "true".into()],
                got: other.into(),
            }),
        }
    }

    fn parse_number<T>(&mut self) -> Result<T, Error>
    where
        T: FromStr,
        Error: From<T::Err>,
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
                    return Err(Error::UnexpectedToken {
                        expected: vec![Token::Name, Token::Number],
                        got: other,
                    })
                }
            }
        }
        let span_str = unsafe { self.tokens.get_span(span) };
        Ok(span_str.parse()?)
    }

    fn parse_char(&mut self) -> Result<char, Error> {
        let span = self.expect(Token::Char)?;
        let inner_span = Span {
            start: span.start + 1,
            end: span.end - 1,
        };
        let len = inner_span.len();
        if len == 0 {
            return Err(Error::InvalidChar("empty"));
        }
        let (ch, parsed, _) = self.parse_char_inner(inner_span)?;
        if parsed < len {
            return Err(Error::InvalidChar("more than one character"));
        }
        Ok(ch)
    }

    fn parse_string(&mut self) -> Result<Cow<str>, Error> {
        let span = self.expect(Token::String)?;
        let start = span.start + 1;
        let end = span.end - 1;

        let mut last_copied = start;
        let mut output = String::new();

        let mut pos = span.start + 1;
        while pos < end {
            let (ch, parsed, is_escape) = self.parse_char_inner(Span { start: pos, end })?;
            if is_escape {
                let chunk = unsafe {
                    self.tokens.get_span(Span {
                        start: last_copied,
                        end: pos,
                    })
                };
                output += chunk;
                output.push(ch);
                last_copied = pos + parsed;
            }
            pos += parsed;
        }
        let last_chunk = unsafe {
            self.tokens.get_span(Span {
                start: last_copied,
                end,
            })
        };
        if output.is_empty() {
            // No escapes; we can just return the input span
            Ok(last_chunk.into())
        } else {
            output += last_chunk;
            Ok(output.into())
        }
    }

    fn parse_list<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        self.expect(Token::LSquare)?;

        let mut elements = vec![];
        loop {
            if let Some((Token::RSquare, _)) = self.peek_next_non_whitespace()? {
                break;
            }
            elements.push(self.parse_value(&ty.list_element_type())?);
            if let (Token::RSquare, _) = self.expect_any_of(&[Token::Comma, Token::RSquare])? {
                break;
            }
        }
        V::make_list(ty, elements).map_err(Error::make_value)
    }

    fn parse_record<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        self.expect(Token::LCurly)?;

        let field_types = ty
            .record_fields()
            .enumerate()
            .map(|(idx, (name, ty))| (name, (idx, ty)))
            .collect::<HashMap<_, _>>();
        let mut values = vec![None; field_types.len()];
        loop {
            if let Some((Token::RCurly, _)) = self.peek_next_non_whitespace()? {
                break;
            }
            let name = self.parse_name()?;

            let (idx, ty) = field_types
                .get(name)
                .ok_or_else(|| Error::RecordFieldUnknown(name.to_string()))?;

            self.expect(Token::Colon)?;

            values[*idx] = Some(self.parse_value(ty)?);

            if let (Token::RCurly, _) = self.expect_any_of(&[Token::Comma, Token::RCurly])? {
                break;
            }
        }
        let fields = ty
            .record_fields()
            .zip(values)
            .map(|((name, ty), maybe_val)| {
                let val = match maybe_val {
                    Some(val) => val,
                    None if ty.kind() == Kind::Option => {
                        V::make_option(&ty, None).map_err(Error::make_value)?
                    }
                    None => return Err(Error::RecordFieldMissing(name.to_string())),
                };
                Ok((name, val))
            })
            .collect::<Result<Vec<_>, _>>()?;
        V::make_record(ty, fields).map_err(Error::make_value)
    }

    fn parse_tuple<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
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
        V::make_tuple(ty, values).map_err(Error::make_value)
    }

    fn parse_variant<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        let name = self.parse_name()?;
        let (case_name, case_ty) = ty
            .variant_cases()
            .find(|(case_name, _)| *case_name == name)
            .ok_or_else(|| Error::UnexpectedName {
                expected: ty.variant_cases().map(|(name, _)| name.into()).collect(),
                got: name.into(),
            })?;
        V::make_variant(ty, case_name, self.parse_maybe_payload(case_ty.as_ref())?)
            .map_err(Error::make_value)
    }

    fn parse_enum<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        let name = self.parse_name()?;
        V::make_enum(ty, name).map_err(Error::make_value)
    }

    fn parse_option<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        let (token, _) =
            self.peek_next_non_whitespace()?
                .ok_or_else(|| Error::UnexpectedToken {
                    expected: vec![Token::Name],
                    got: None,
                })?;

        let some_ty = ty.option_some_type();
        let val = if token == Token::Name {
            match self.parse_name()? {
                "some" => self.parse_maybe_payload(Some(&some_ty))?,
                "none" => None,
                other => {
                    return Err(Error::UnexpectedName {
                        expected: vec!["some".into(), "none".into()],
                        got: other.into(),
                    })
                }
            }
        } else {
            // Flattened `some` value
            if some_ty.kind() == Kind::Option {
                return Err(Error::InvalidFlattening(Kind::Result));
            }
            Some(self.parse_value(&some_ty)?)
        };
        V::make_option(ty, val).map_err(Error::make_value)
    }

    fn parse_result<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        let (token, _) =
            self.peek_next_non_whitespace()?
                .ok_or_else(|| Error::UnexpectedToken {
                    expected: vec![Token::Name],
                    got: None,
                })?;

        let (ok_ty, err_ty) = ty.result_types();
        let (val, is_ok) = if token == Token::Name {
            let (payload_ty, is_ok) = match self.parse_name()? {
                "ok" => (ok_ty, true),
                "err" => (err_ty, false),
                other => {
                    return Err(Error::UnexpectedName {
                        expected: vec!["ok".into(), "err".into()],
                        got: other.into(),
                    })
                }
            };
            let val = self.parse_maybe_payload(payload_ty.as_ref())?;
            (val, is_ok)
        } else if let Some(ty) = ok_ty {
            // Flattened `ok` value
            if ty.kind() == Kind::Result {
                return Err(Error::InvalidFlattening(Kind::Result));
            }
            let val = self.parse_value(&ty)?;
            (Some(val), true)
        } else {
            return Err(Error::UnexpectedToken {
                expected: vec![Token::Name],
                got: Some(token),
            });
        };

        V::make_result(ty, if is_ok { Ok(val) } else { Err(val) }).map_err(Error::make_value)
    }

    fn parse_flags<V: Val>(&mut self, ty: &V::Type) -> Result<V, Error> {
        self.expect(Token::LCurly)?;
        let mut flags = vec![];
        loop {
            if let Some((Token::RCurly, _)) = self.peek_next_non_whitespace()? {
                break;
            }
            let name = self.parse_name()?;
            let flag = ty.flags_names().find(|flag| *flag == name).ok_or_else(|| {
                Error::UnexpectedName {
                    expected: ty.flags_names().map(Into::into).collect(),
                    got: name.into(),
                }
            })?;
            flags.push(flag);
            if let (Token::RCurly, _) = self.expect_any_of(&[Token::Comma, Token::RCurly])? {
                break;
            }
        }
        V::make_flags(ty, flags).map_err(Error::make_value)
    }

    fn next_non_whitespace(&mut self) -> Result<Option<(Token, Span)>, Error> {
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

    fn peek_next_non_whitespace(&mut self) -> Result<Option<(Token, Span)>, Error> {
        self.peeked = self.next_non_whitespace()?;
        Ok(self.peeked.clone())
    }

    fn expect_any_of(&mut self, expected: &[Token]) -> Result<(Token, Span), Error> {
        if let Some((token, span)) = self.next_non_whitespace()? {
            if expected.contains(&token) {
                Ok((token, span))
            } else {
                Err(Error::UnexpectedToken {
                    expected: expected.to_vec(),
                    got: Some(token),
                })
            }
        } else {
            Err(Error::UnexpectedToken {
                expected: expected.to_vec(),
                got: None,
            })
        }
    }

    fn expect(&mut self, expected: Token) -> Result<Span, Error> {
        let (_, span) = self.expect_any_of(&[expected])?;
        Ok(span)
    }

    // Parse a character within a char or string literal. Also returns the
    // number of bytes parsed and whether it was an escape.
    fn parse_char_inner(&self, span: Span) -> Result<(char, usize, bool), Error> {
        let span_str = unsafe { self.tokens.get_span(span) };
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
            'x' => {
                let mut nibbles = chars.map(|ch| ch.to_digit(16));
                let (Some(Some(h)), Some(Some(l))) = (nibbles.next(), nibbles.next()) else {
                    return Err(Error::InvalidEscape(
                        span_str.chars().skip(1).take(3).collect(),
                    ));
                };
                Ok(((h << 4 | l).try_into().unwrap(), 4, true))
            }
            other => Err(Error::InvalidEscape(other.to_string())),
        }
    }

    fn parse_name(&mut self) -> Result<&str, Error> {
        let span = self.expect(Token::Name)?;
        Ok(unsafe { self.tokens.get_span(span) })
    }

    fn parse_maybe_payload<V: Val>(&mut self, ty: Option<&V::Type>) -> Result<Option<V>, Error> {
        if let Some(ty) = ty {
            self.expect(Token::LParen)?;
            let val = self.parse_value(ty)?;
            self.expect(Token::RParen)?;
            Ok(Some(val))
        } else {
            Ok(None)
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("invalid char: {0}")]
    InvalidChar(&'static str),
    #[error("invalid escape: `\\{0}`")]
    InvalidEscape(String),
    #[error("cannot flatten nested {0:?}s")]
    InvalidFlattening(Kind),
    #[error("invalid token: {0}")]
    Lex(#[from] crate::lex::Error),
    #[error("error constructing value: {0}")]
    MakeValueError(String),
    #[error("error parsing int: {0}")]
    ParseInt(#[from] ParseIntError),
    #[error("error parsing float: {0}")]
    ParseFloat(#[from] ParseFloatError),
    #[error("duplicate field `{0}`")]
    RecordFieldDuplicated(String),
    #[error("missing field `{0}`")]
    RecordFieldMissing(String),
    #[error("unknown field `{0}`")]
    RecordFieldUnknown(String),
    #[error("expected {expected:?}, got {got:?}")]
    UnexpectedName { expected: Vec<String>, got: String },
    #[error("expected {expected:?}, got {got:?}")]
    UnexpectedToken {
        expected: Vec<Token>,
        got: Option<Token>,
    },
    #[error("unsupported type {0}")]
    Unsupported(String),
}

impl Error {
    fn make_value(err: impl Display) -> Self {
        Self::MakeValueError(err.to_string())
    }
}

#[cfg(test)]
mod tests {
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
            (r"'\x00'", Val::Char('\0')),
            (r"'\x1b'", Val::Char('\x1b')),
            (r"'\x7F'", Val::Char('\x7f')),
            (r#""abc""#, Val::String("abc".into())),
            (r#""☃\\\"\n""#, Val::String("☃\\\"\n".into())),
            (r#""\x00\x7f""#, Val::String("\x00\x7F".into())),
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

    fn parse_unwrap<V: Val>(input: &str, ty: V::Type) -> V {
        Parser::new(input)
            .parse_value(&ty)
            .unwrap_or_else(|err| panic!("error decoding {input:?}: {err}"))
    }
}
