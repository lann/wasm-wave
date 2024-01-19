use std::borrow::Cow;

use crate::{ast::Node, lex::Keyword, parser::ParserError, Parser, WasmValue};

/// An UntypedValue represents a parsed but not type-checked WAVE value.
#[derive(Debug)]
pub struct UntypedValue<'source> {
    source: Cow<'source, str>,
    node: Node,
}

impl<'source> UntypedValue<'source> {
    pub(crate) fn new(source: impl Into<Cow<'source, str>>, node: Node) -> Self {
        Self {
            source: source.into(),
            node,
        }
    }

    /// Parse an untyped value from WAVE.
    pub fn parse(source: &'source str) -> Result<Self, ParserError> {
        let mut parser = Parser::new(source);
        let val = parser.parse_raw_value()?;
        parser.finish()?;
        Ok(val)
    }

    /// Creates an owned value, copying if necessary.
    pub fn into_owned(self) -> UntypedValue<'static> {
        UntypedValue::new(self.source.into_owned(), self.node)
    }

    /// Converts this untyped value into the given typed value.
    pub fn to_wasm_value<V: WasmValue>(&self, ty: &V::Type) -> Result<V, ParserError> {
        self.node.to_wasm_value(ty, &self.source)
    }

    /// Converts this untyped tuple value into the given parameter types.
    /// See [`Parser::parse_func_call`].
    pub fn to_wasm_params<'types, V: WasmValue + 'static>(
        &self,
        types: impl IntoIterator<Item = &'types V::Type>,
    ) -> Result<Vec<V>, ParserError> {
        self.node().to_wasm_params(types, self.source())
    }

    /// Returns the source this value was parsed from.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Returns this value's root node.
    pub fn node(&self) -> &Node {
        &self.node
    }
}

impl std::fmt::Display for UntypedValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_node(f, &self.node, &self.source)
    }
}

fn fmt_node(f: &mut impl std::fmt::Write, node: &Node, src: &str) -> std::fmt::Result {
    use crate::ast::NodeType::*;
    match node.ty() {
        BoolTrue | BoolFalse | Number | Char | String | Label => {
            write!(f, "{}", &src[node.span()])
        }
        Tuple => {
            f.write_char('(')?;
            let mut first = true;
            for element in node.as_tuple()? {
                if first {
                    first = false;
                } else {
                    f.write_str(", ")?;
                }
                fmt_node(f, element, src)?;
            }
            f.write_char(')')
        }
        List => {
            f.write_char('[')?;
            let mut first = true;
            for element in node.as_list()? {
                if first {
                    first = false;
                } else {
                    f.write_str(", ")?;
                }
                fmt_node(f, element, src)?;
            }
            f.write_char(']')
        }
        Record => {
            f.write_char('{')?;
            let mut first = true;
            for (name, value) in node.as_record(src)? {
                if first {
                    first = false;
                } else {
                    f.write_str(", ")?;
                }
                write!(f, "{name}: ")?;
                fmt_node(f, value, src)?;
            }
            if first {
                f.write_char(':')?;
            }
            f.write_char('}')
        }
        VariantWithPayload => {
            let (label, payload) = node.as_variant(src)?;
            if Keyword::from_label(label).is_some() {
                f.write_char('%')?;
            }
            // TODO: '%'-escape some label (?)
            fmt_variant(f, label, payload, src)
        }
        OptionSome => fmt_variant(f, "some", node.as_option()?, src),
        OptionNone => fmt_variant(f, "none", None, src),
        ResultOk => fmt_variant(f, "ok", node.as_result()?.unwrap(), src),
        ResultErr => fmt_variant(f, "err", node.as_result()?.unwrap_err(), src),
        Flags => {
            f.write_char('{')?;
            let mut first = true;
            for flag in node.as_flags(src)? {
                if first {
                    first = false;
                } else {
                    f.write_str(", ")?;
                }
                f.write_str(flag)?;
            }
            f.write_char('}')
        }
    }
}

fn fmt_variant(
    f: &mut impl std::fmt::Write,
    label: &str,
    payload: Option<&Node>,
    src: &str,
) -> std::fmt::Result {
    f.write_str(label)?;
    if let Some(node) = payload {
        f.write_char('(')?;
        fmt_node(f, node, src)?;
        f.write_char(')')?;
    }
    Ok(())
}

impl From<ParserError> for std::fmt::Error {
    fn from(_: ParserError) -> Self {
        Self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips() {
        for src in [
            "true",
            "18446744073709551616",
            "-9223372036854775808",
            "[-3.1415, 0, inf, nan, -inf]",
            "['☃', '\\n']",
            r#""☃☃☃""#,
            "(1, false)",
            "{:}",
            "{code: red}",
            "left(1)",
            "[some(1), none]",
            "[ok(1), err(2)]",
            "[ok, err]",
            "%inf(inf)",
            "%some",
            "%none(none)",
        ] {
            let val = UntypedValue::parse(src).unwrap();
            let encoded = val.to_string();
            assert_eq!(encoded, src);
        }
    }
}
