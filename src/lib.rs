//! Web Assembly Value Encoding
//!
//! <https://github.com/lann/wave>
#![deny(missing_docs)]

pub mod fmt;
pub mod func;
pub mod parser;
pub mod value;
pub mod writer;

mod lex;
mod ty;
mod val;

/// Completion API
pub mod completion;
#[cfg(feature = "wasmtime")]
/// Implementations for [`wasmtime`] types.
pub mod wasmtime;

pub use ty::{WasmType, WasmTypeKind};
pub use val::WasmValue;

use parser::Parser;
use writer::Writer;

/// Parses a [`WasmValue`] from the given WAVE-encoded string.
/// ```
/// use wasmtime::component::{Type, Val};
/// # fn main() -> Result<(), wasm_wave::parser::ParserError> {
/// let val: Val = wasm_wave::from_str(&Type::Char, r"'\u{1F44B}'")?;
/// assert_eq!(val, Val::Char('👋'));
/// # Ok(())
/// # }
/// ```
pub fn from_str<V: WasmValue>(ty: &V::Type, s: &str) -> Result<V, parser::ParserError> {
    Parser::new(s).parse_value(ty)
}

/// WAVE-encodes a [`WasmValue`] into a string.
/// ```
/// use wasmtime::component::Val;
/// # fn main() -> Result<(), wasm_wave::writer::WriterError> {
/// let wave_str = wasm_wave::to_string(&Val::Char('\u{1F44B}'))?;
/// assert_eq!(wave_str, "'👋'");
/// # Ok(())
/// # }
pub fn to_string(val: &impl WasmValue) -> Result<String, writer::WriterError> {
    let mut buf = vec![];
    Writer::new(&mut buf).write_value(val)?;
    Ok(String::from_utf8(buf).unwrap_or_else(|err| panic!("invalid UTF-8: {err:?}")))
}
