//! Web Assembly Value Encoding
//!
//! <https://github.com/lann/wave>
#![deny(missing_docs)]

mod lex;
mod ty;
mod val;

#[cfg(feature = "wasmtime")]
mod wasmtime;

pub mod fmt;
pub mod parser;
pub mod value;
pub mod writer;

use parser::Parser;
pub use ty::{Kind, Type};
pub use val::Val;
use writer::Writer;

/// Parses a [`Val`] from the given WAVE-encoded string.
/// ```
/// use wasmtime::component::{Type, Val};
/// # fn main() -> Result<(), wasm_wave::parser::ParserError> {
/// let val: Val = wasm_wave::from_str(&Type::Char, r"'\u{1F44B}'")?;
/// assert_eq!(val, Val::Char('👋'));
/// # Ok(())
/// # }
/// ```
pub fn from_str<V: Val>(ty: &V::Type, s: &str) -> Result<V, parser::ParserError> {
    Parser::new(s).parse_value(ty)
}

/// WAVE-encodes a [`Val`] into a string.
/// ```
/// use wasmtime::component::Val;
/// # fn main() -> Result<(), wasm_wave::writer::WriterError> {
/// let wave_str = wasm_wave::to_string(&Val::Char('\u{1F44B}'))?;
/// assert_eq!(wave_str, "'👋'");
/// # Ok(())
/// # }
pub fn to_string(val: &impl Val) -> Result<String, writer::WriterError> {
    let mut buf = vec![];
    Writer::new(&mut buf).write_value(val)?;
    Ok(String::from_utf8(buf).unwrap_or_else(|err| panic!("invalid UTF-8: {err:?}")))
}
