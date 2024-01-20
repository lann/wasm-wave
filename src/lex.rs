//! Wave lexer

use std::fmt::Display;

use logos::{Lexer, Logos, Span};

/// Represents a WAVE token.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Logos)]
#[logos(error = LexingError)]
#[logos(skip r"[ \t\n\r]+")]
#[logos(subpattern label_word = r"[a-z][a-z0-9]*|[A-Z][A-Z0-9]*")]
#[logos(subpattern char_escape = r#"\\['"tnr\\]|\\u\{[0-9a-fA-F]{1,6}\}"#)]
pub enum Token {
    /// The `{` symbol.
    #[token("{")]
    BraceOpen,
    /// The `}` symbol.
    #[token("}")]
    BraceClose,

    /// The `(` symbol.
    #[token("(")]
    ParenOpen,
    /// The `)` symbol.
    #[token(")")]
    ParenClose,

    /// The `[` symbol.
    #[token("[")]
    BracketOpen,
    /// The `]` symbol.
    #[token("]")]
    BracketClose,

    /// The `:` symbol.
    #[token(":")]
    Colon,

    /// The `,` symbol.
    #[token(",")]
    Comma,

    /// A number literal.
    #[regex(r"-?(0|([1-9][0-9]*))(\.[0-9]+)?([eE][-+]?[0-9]+)?")]
    #[token("-inf")]
    Number,

    /// A label.
    #[regex(r"%?(?&label_word)(-(?&label_word))*")]
    Label,

    /// A char literal.
    #[regex(r#"'([^\\']{1,4}|(?&char_escape))'"#, validate_char)]
    Char,

    /// A string literal.
    #[regex(r#""([^\\"]|(?&char_escape))*""#)]
    String,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

fn validate_char(lex: &mut Lexer<Token>) -> Result<(), LexingError> {
    let s = &lex.slice()[1..lex.slice().len() - 1];
    if s.starts_with('\\') || s.chars().count() == 1 {
        Ok(())
    } else {
        Err(LexingError::InvalidChar(lex.span()))
    }
}

pub(crate) enum Keyword {
    True,
    False,
    Some,
    None,
    Ok,
    Err,
    Inf,
    Nan,
}

impl Keyword {
    pub fn from_label(raw_label: &str) -> Option<Self> {
        Some(match raw_label {
            "true" => Self::True,
            "false" => Self::False,
            "some" => Self::Some,
            "none" => Self::None,
            "ok" => Self::Ok,
            "err" => Self::Err,
            "inf" => Self::Inf,
            "nan" => Self::Nan,
            _ => return None,
        })
    }
}

/// WAVE lexing errors
#[derive(Default, Debug, Clone, PartialEq)]
pub enum LexingError {
    /// Invalid char token.
    InvalidChar(Span),
    /// Invalid token.
    #[default]
    InvalidToken,
}

impl Display for LexingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidToken => write!(f, "invalid token"),
            Self::InvalidChar(span) => write!(f, "invalid char literal at {span:?}"),
        }
    }
}
impl std::error::Error for LexingError {}
