use crate::{
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
        Err(ParserError::UnexpectedEnd { completion }) => completion,
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
        let partial = partial.trim_start();
        use crate::WasmTypeKind::*;
        let candidates = match ty.kind() {
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
            Option => variant_completions(partial, ["some", "none"]),
            Result => variant_completions(partial, ["ok", "err"]),
            // TODO: These will require some more work.
            Flags => vec![],
            Record => vec![],
            Unsupported => vec![],
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
    fn test_options() {
        let ty = Type::option(Type::BOOL);
        assert_candidates("", &ty, &["some", "none"]);
        assert_candidates("so", &ty, &["me"]);
        assert_candidates("some", &ty, &["("]);
    }

    fn assert_candidates(input: &str, ty: &Type, expected: &[&str]) {
        let candidates = completions(ty, input)
            .unwrap_or_else(|| panic!("no completions for {ty:?}, {input:?}"))
            .candidates;
        assert_eq!(candidates, expected, "for {input:?}");
    }
}
