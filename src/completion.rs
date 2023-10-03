use crate::{
    lex::Token,
    parser::{Parser, ParserError},
    value::{Type, Value},
    WasmType,
};

/// Returns [`Completions`] for parsing the given `input` as the given
/// [`WasmType`]. Returns None if the given type is unsupported or invalid,
/// or if there is a parsing error that does not allow completion (e.g. an
/// error before the end of the input).
pub fn completions(ty: &impl WasmType, input: &str) -> Option<Completions> {
    let ty = Type::from_wasm_type(ty)?;
    let mut parser = Parser::new(input);
    parser.completion(true);
    match parser.parse_value::<Value>(&ty) {
        Err(ParserError::UnexpectedEnd { completions, .. }) => completions,
        _ => None,
    }
}

/// Returns [`Completions`] for parsing the given `input` as the given
/// [`WasmType`] params. Returns None if any of the given params are unsupported
/// or invalid, or if there is a parsing error that does not allow completion
/// (e.g. an error before the end of the input).
pub fn params_completions<T: WasmType>(
    params: impl IntoIterator<Item = T>,
    input: &str,
) -> Option<Completions> {
    let types = params
        .into_iter()
        .map(|ty| Type::from_wasm_type(&ty))
        .collect::<Option<Vec<_>>>()?;
    let mut parser = Parser::new(input);
    parser.completion(true);
    match parser.parse_params::<Value>(types.iter()) {
        Err(ParserError::UnexpectedEnd { completions, .. }) => completions,
        _ => None,
    }
}

/// Provides recommendations for (partially) completing an incomplete input.
/// See [`Parser::completion`](crate::Parser::completion).
#[derive(Debug)]
pub struct Completions {
    partial: String,
    candidates: Vec<String>,
}

impl Completions {
    pub(crate) fn new(partial: &str, err: &ParserError, ty: Option<&impl WasmType>) -> Self {
        use ParserError::*;
        let candidates = match err {
            UnexpectedName { expected, got } => replacement_candidates(got, expected),
            UnexpectedToken {
                expected,
                got: None,
            } => token_candidates(expected),
            _ => {
                if let Some(ty) = ty {
                    type_candidates(partial, ty)
                } else {
                    vec![]
                }
            }
        };
        Completions {
            partial: partial.into(),
            candidates,
        }
    }

    /// Returns the partial input prefix being completed.
    pub fn partial(&self) -> &str {
        &self.partial
    }

    /// Returns an iterator of completion candidates.
    pub fn candidates(&self) -> impl Iterator<Item = &str> {
        self.candidates.iter().map(|c| c.as_str())
    }
}

fn type_candidates(partial: &str, ty: &impl WasmType) -> Vec<String> {
    let partial = partial.trim_start();
    use crate::WasmTypeKind::*;
    match ty.kind() {
        Char => string_like_completions(partial, "'"),
        String => string_like_completions(partial, "\""),
        _ => vec![],
    }
}

fn replacement_candidates<T: AsRef<str>>(
    partial: &str,
    replacements: impl IntoIterator<Item = T>,
) -> Vec<String> {
    replacements
        .into_iter()
        .flat_map(|replace| {
            if let Some(suffix) = replace.as_ref().strip_prefix(partial) {
                if !suffix.is_empty() {
                    return Some(suffix.into());
                }
            }
            None
        })
        .collect()
}

fn string_like_completions(partial: &str, delim: &'static str) -> Vec<String> {
    // TODO: be more precise about escape detection
    if partial.ends_with('\\') {
        vec![delim, "\\", "t", "n", "r", "u"]
    } else if partial.ends_with("\\u") {
        vec!["{"]
    } else if partial.is_empty() || partial.len() > 1 {
        vec![delim]
    } else {
        vec![]
    }
    .into_iter()
    .map(Into::into)
    .collect()
}

fn token_candidates(tokens: &[Token]) -> Vec<String> {
    tokens
        .iter()
        .filter_map(|tok| {
            tok.as_char()
                .or(match tok {
                    Token::Number => Some('0'),
                    Token::Char => Some('\''),
                    Token::String => Some('"'),
                    _ => None,
                })
                .map(Into::into)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_types() {
        for (input, ty, expected_candidates) in [
            ("", Type::BOOL, &["true", "false"][..]),
            ("t", Type::BOOL, &["rue"]),
            (" t", Type::BOOL, &["rue"]),
            ("fa", Type::BOOL, &["lse"]),
            ("maybe", Type::BOOL, &[]),
            ("", Type::U8, &["0"]),
            ("", Type::S8, &["0", "-"]),
            ("'", Type::CHAR, &[]),
            ("'\\", Type::CHAR, &["'", "\\", "t", "n", "r", "u"]),
            ("'\\u", Type::CHAR, &["{"]),
            ("'x", Type::CHAR, &["'"]),
            ("", Type::STRING, &["\""]),
            ("\"abc", Type::STRING, &["\""]),
        ] {
            assert_candidates(input, &ty, expected_candidates);
        }
    }

    #[test]
    fn test_lists() {
        let ty = Type::list(Type::BOOL);
        assert_candidates("", &ty, &["["]);
        assert_candidates("[", &ty, &["true", "false"]);
        assert_candidates("[true", &ty, &[",", "]"]);
        assert_candidates("[true, fa", &ty, &["lse"]);
        assert_candidates("[true, false", &ty, &[",", "]"]);
    }

    #[test]
    fn test_records() {
        let ty = Type::record([("first", Type::BOOL), ("second", Type::BOOL)]).unwrap();
        assert_candidates("", &ty, &["{"]);
        assert_candidates("{", &ty, &["first", "second"]);
        assert_candidates("{f", &ty, &["irst"]);
        assert_candidates("{first", &ty, &[":"]);
        assert_candidates("{first:", &ty, &["true", "false"]);
        assert_candidates("{first: t", &ty, &["rue"]);
        assert_candidates("{first: true", &ty, &[","]);
        assert_candidates("{first: true,", &ty, &["second"]);
        assert_candidates("{first: true, s", &ty, &["econd"]);
        assert_candidates("{first: true, second: false", &ty, &["}", ","]);
    }

    #[test]
    fn test_tuples() {
        let ty = Type::tuple([Type::BOOL, Type::BOOL]).unwrap();
        assert_candidates("", &ty, &["("]);
        assert_candidates("(", &ty, &["true", "false"]);
        assert_candidates("(true, fa", &ty, &["lse"]);
    }

    #[test]
    fn test_enum() {
        let ty = Type::enum_ty(["no", "nope", "nein"]).unwrap();
        assert_candidates("", &ty, &["no", "nope", "nein"]);
        assert_candidates("n", &ty, &["o", "ope", "ein"]);
        assert_candidates("nop", &ty, &["e"]);
    }

    #[test]
    fn test_variants() {
        let ty = Type::variant([("unset", None), ("set", Some(Type::BOOL))]).unwrap();
        assert_candidates("", &ty, &["unset", "set"]);
        assert_candidates("u", &ty, &["nset"]);
        assert_candidates("set", &ty, &["("]);
        assert_candidates("set(", &ty, &["true", "false"]);
        assert_candidates("set(t", &ty, &["rue"]);
        assert_candidates("set(true", &ty, &[")"]);
    }

    #[test]
    fn test_options() {
        let ty = Type::option(Type::BOOL);
        assert_candidates("", &ty, &["true", "false"]);
        assert_candidates("t", &ty, &["rue"]);
        assert_candidates("s", &ty, &["ome"]);
        assert_candidates("n", &ty, &["one"]);
        assert_candidates("some", &ty, &["("]);
        assert_candidates("some(", &ty, &["true", "false"]);
    }

    #[test]
    fn test_results() {
        let ty = Type::result(Some(Type::BOOL), None);
        assert_candidates("", &ty, &["true", "false"]);
        assert_candidates("t", &ty, &["rue"]);
        assert_candidates("o", &ty, &["k"]);
        assert_candidates("e", &ty, &["rr"]);
        assert_candidates("ok", &ty, &["("]);
    }

    #[test]
    fn test_flags() {
        let ty = Type::flags(["read", "write"]).unwrap();
        assert_candidates("", &ty, &["{"]);
        assert_candidates("{", &ty, &["read", "write"]);
        assert_candidates("{r", &ty, &["ead"]);
        assert_candidates("{read", &ty, &["}", ","]);
        assert_candidates("{read,", &ty, &["write"]);
        assert_candidates("{read, w", &ty, &["rite"]);
        assert_candidates("{read, write", &ty, &["}", ","]);
        assert_candidates("{write, ", &ty, &["read"]);
    }

    #[test]
    fn test_params_completion() {
        let params = [Type::BOOL, Type::option(Type::BOOL)];
        for (input, expected_candidates) in [
            ("(", &["true", "false"][..]),
            ("(t", &["rue"]),
            ("(true", &[",", ")"]),
            ("(true, ", &["true", "false"]),
            ("(true, f", &["alse"]),
        ] {
            let candidates = params_completions(params.clone(), input)
                .unwrap_or_else(|| panic!("no completions for {input:?}"))
                .candidates;
            assert_eq!(candidates, expected_candidates, "for {input:?}");
        }
    }

    #[test]
    fn test_flat_string_param_completion() {
        let params = [Type::option(Type::STRING)];
        let candidates = params_completions(params, "(\"\\u").unwrap().candidates;
        assert_eq!(candidates, ["{"]);
    }

    fn assert_candidates(input: &str, ty: &Type, expected: &[&str]) {
        let candidates = completions(ty, input)
            .unwrap_or_else(|| panic!("no completions for {ty:?}, {input:?}"))
            .candidates;
        assert_eq!(candidates, expected, "for {input:?}");
    }
}
