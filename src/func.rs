//! Web Assembly Value Encoding func encodings.

use std::borrow::Cow;

use crate::{parser::ParserError, WasmType};

/// Represents an unparsed Web Assembly func call.
pub struct CallExpr<'a> {
    /// The func name
    pub func_name: &'a str,
    /// The func args, including surrounding parens
    pub args: &'a str,
}

impl<'a> CallExpr<'a> {
    /// Returns a func expr parsed from the given `expr`.
    pub fn parse(expr: &'a str) -> Result<Self, ParserError> {
        let paren_idx = expr
            .find('(')
            .ok_or_else(|| ParserError::ParseParams("no opening paren in call expr".into()))?;
        let (name, args) = expr.split_at(paren_idx);
        let func_name = name.trim();
        let args = args.trim();
        if !args.ends_with(')') {
            return Err(ParserError::ParseParams(
                "no closing paren in call expr".into(),
            ));
        }
        Ok(Self { func_name, args })
    }
}

/// The WasmFunc trait may be implemented to represent Wasm func type
/// signatures to be (de)serialized with WAVE.
pub trait WasmFunc {
    /// A type representing types of these params and results.
    type Type: WasmType;

    /// Returns an iterator of the func's parameter types.
    fn params(&self) -> Box<dyn Iterator<Item = Self::Type> + '_>;

    /// Returns an iterator of the func's parameter names. Must be the same
    /// length as the iterator returned by `params` or empty if this WasmFunc
    /// impl does not support param names.
    fn param_names(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        Box::new(std::iter::empty())
    }

    /// Returns an iterator of the func's result types.
    fn results(&self) -> Box<dyn Iterator<Item = Self::Type> + '_>;

    /// Returns an iterator of the func's result names. Must be the same
    /// length as the iterator returned by `results` or empty if there are no
    /// named results or if this WasmFunc impl does not support result names.
    fn result_names(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        Box::new(std::iter::empty())
    }
}
