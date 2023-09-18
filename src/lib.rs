mod component;
mod core;
mod ty;
mod val;

pub mod lex;
pub mod parser;
pub mod writer;

use parser::Parser;
pub use ty::Type;
pub use val::Val;
use writer::Writer;

pub fn from_str<V: Val>(ty: &V::Type, s: &str) -> Result<V, parser::Error> {
    Parser::new(s).parse_value(ty)
}

pub fn to_string(val: &impl Val) -> Result<String, writer::Error> {
    let mut buf = vec![];
    Writer::new(&mut buf).write_value(val)?;
    String::from_utf8(buf).map_err(|err| writer::Error::Other(format!("invalid UTF-8: {err:?}")))
}
