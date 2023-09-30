use crate::{
    parser::{flattenable, Parser, ParserError, ERR, NONE, OK, SOME},
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
        Err(ParserError::UnexpectedEnd {
            completions: completion,
        }) => completion,
        _ => None,
    }
}

/// Returns [`Completions`] for parsing the given `input` as the given
/// [`WasmType`] params. Returns None if any of the given params are unsupported
/// or invalid, or if there is a parsing error that does not allow completion
/// (e.g. an error before the end of the input).
pub fn params_completions<'ty, T: WasmType + 'static>(
    params: impl IntoIterator<Item = &'ty T>,
    input: &str,
) -> Option<Completions> {
    let types = params
        .into_iter()
        .map(Type::from_wasm_type)
        .collect::<Option<Vec<_>>>()?;
    let mut parser = Parser::new(input);
    parser.completion(true);
    match parser.parse_params::<Value>(types.iter()) {
        Err(ParserError::UnexpectedEnd {
            completions: completion,
        }) => completion,
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
    pub(crate) fn new(ty: &impl WasmType, partial: &str) -> Self {
        Completions {
            partial: partial.into(),
            candidates: type_candidates(partial, ty),
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
        Bool => replacement_candidates(partial, ["true", "false"]),
        S8 | S16 | S32 | S64 | U8 | U16 | U32 | U64 | Float32 | Float64 => {
            // TODO: better e.g. float completions
            replacement_candidates(partial, ["0"])
        }
        Char => string_like_completions(partial, "'"),
        String => string_like_completions(partial, "\""),
        List => list_like_completions(partial, "[", "]"),
        Tuple => list_like_completions(partial, "(", ")"), // TODO: actually count elements
        Enum => replacement_candidates(partial, ty.enum_cases()),
        Variant => variant_completions(partial, ty.variant_cases().map(|(name, _)| name)),
        Option => bare_completions(partial, Some(ty.option_some_type().unwrap()), [SOME, NONE]),
        Result => bare_completions(partial, ty.result_types().unwrap().0, [OK, ERR]),
        // TODO: These will require some more work.
        Flags => vec![],
        Record => vec![],
        Unsupported => vec![],
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

fn variant_completions<T: Into<String>>(
    partial: &str,
    names: impl IntoIterator<Item = T>,
) -> Vec<String> {
    let names = names.into_iter().map(|n| n.into()).collect::<Vec<_>>();
    if names.contains(&partial.to_string()) {
        vec!["(".into()]
    } else if partial.contains('(') {
        vec![")".into()]
    } else {
        replacement_candidates(partial, &names)
    }
}

fn bare_completions(
    partial: &str,
    bare_type: Option<impl WasmType>,
    cases: [&'static str; 2],
) -> Vec<String> {
    let candidates = variant_completions(partial, cases);
    if !candidates.is_empty() {
        return candidates;
    }
    if let Some(ty) = bare_type {
        if flattenable(ty.kind()) {
            return type_candidates(partial, &ty);
        }
    }
    vec![]
}

fn list_like_completions(partial: &str, open: &'static str, close: &'static str) -> Vec<String> {
    if partial.is_empty() {
        vec![open.into()]
    } else {
        vec![",".into(), close.into()]
    }
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
    fn test_params_completion() {
        let params = [Type::BOOL, Type::option(Type::BOOL)];
        for (input, expected_candidates) in [
            ("(", &["true", "false"][..]),
            ("(t", &["rue"]),
            ("(true, ", &["true", "false"]),
            ("(true, f", &["alse"]),
        ] {
            let candidates = params_completions(params.iter(), input)
                .unwrap_or_else(|| panic!("no completions for {input:?}"))
                .candidates;
            assert_eq!(candidates, expected_candidates, "for {input:?}");
        }
    }

    fn assert_candidates(input: &str, ty: &Type, expected: &[&str]) {
        let candidates = completions(ty, input)
            .unwrap_or_else(|| panic!("no completions for {ty:?}, {input:?}"))
            .candidates;
        assert_eq!(candidates, expected, "for {input:?}");
    }
}
