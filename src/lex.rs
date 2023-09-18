use std::{ops::Range, str::Chars};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token {
    Whitespace,

    Colon,
    Comma,
    Dash,
    LCurly,
    RCurly,
    LParen,
    RParen,
    LSquare,
    RSquare,

    Name,
    Number,
    Char,
    String,
}

pub type Span = Range<usize>;

pub struct Tokenizer<'a> {
    input: &'a str,
    // Invariant: pos must point at a char boundary within input
    pos: usize,
}

impl<'a> Tokenizer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    /// # Safety
    /// May only be passed spans that are valid for the input, such as those
    /// returned from this Tokenizer.
    pub unsafe fn get_span(&self, span: Span) -> &str {
        self.input.get_unchecked(span)
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn next_token(&mut self) -> Result<Option<Token>, Error> {
        debug_assert!(self.pos <= self.input.len());

        let mut chars = self.next_chars();
        let Some(ch) = chars.next() else {
            return Ok(None);
        };

        if ch.is_whitespace() {
            self.eat_while(|ch| ch.is_whitespace());
            return Ok(Some(Token::Whitespace));
        }

        // Single char tokens
        if let Some(token) = match ch {
            ':' => Some(Token::Colon),
            ',' => Some(Token::Comma),
            '-' => Some(Token::Dash),
            '{' => Some(Token::LCurly),
            '}' => Some(Token::RCurly),
            '(' => Some(Token::LParen),
            ')' => Some(Token::RParen),
            '[' => Some(Token::LSquare),
            ']' => Some(Token::RSquare),
            _ => None,
        } {
            // `pos` invariant holds because we increment by `len_utf8`
            self.pos += ch.len_utf8();
            return Ok(Some(token));
        }

        // Multi-char tokens
        let token = match ch {
            'a'..='z' | 'A'..='Z' => {
                // Eat characters from kebab-names (ascii alphanumeric and dash)
                self.eat_while(|ch| ch.is_ascii_alphanumeric() || ch == '-');
                Token::Name
            }
            '0'..='9' => {
                // Eat characters from numbers (including decimals and exponents)
                self.eat_while(|ch| matches!(ch, '0'..='9' | '-' | '.' | 'e' | 'E' | '+'));
                Token::Number
            }
            '\'' => {
                self.eat_string('\'')?;
                Token::Char
            }
            '"' => {
                self.eat_string('"')?;
                Token::String
            }
            _ => return Err(Error::UnexpectedChar(self.pos)),
        };
        Ok(Some(token))
    }

    fn next_chars(&self) -> Chars<'a> {
        // Safe because of `pos` invariant
        unsafe { self.input.get_unchecked(self.pos..) }.chars()
    }

    fn eat_while(&mut self, f: impl Fn(char) -> bool) {
        // `pos` invariant holds because we count by `len_utf8`
        self.pos += self
            .next_chars()
            .map_while(|ch| f(ch).then(|| ch.len_utf8()))
            .sum::<usize>();
    }

    // Eat a string (one delimiter to the next, including any backslash-escaped delimiters)
    fn eat_string(&mut self, delim: char) -> Result<(), Error> {
        let mut chars = self.next_chars();

        let first = chars.next().unwrap();
        debug_assert_eq!(first, delim);
        self.pos += first.len_utf8();

        let mut escaping = false;
        for ch in chars {
            // `pos` invariant holds because we count by `len_utf8`
            self.pos += ch.len_utf8();
            if escaping {
                escaping = false;
            } else if ch == '\\' {
                escaping = true;
            } else if ch == delim {
                return Ok(());
            }
        }
        Err(Error::UnexpectedEnd)
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<(Token, Span), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.pos();
        match self.next_token() {
            Ok(Some(token)) => {
                let span = Span {
                    start,
                    end: self.pos,
                };
                Some(Ok((token, span)))
            }
            Ok(None) => None,
            Err(err) => Some(Err(err)),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("unexpected character at position {0}")]
    UnexpectedChar(usize),
    #[error("unexpected end of input")]
    UnexpectedEnd,
}
