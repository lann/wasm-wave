//! Web Assembly Value Encoding writer.

use std::{fmt::Debug, io::Write};

use thiserror::Error;

use crate::{
    lex::Keyword,
    ty::{WasmType, WasmTypeKind},
    val::WasmValue,
};

/// A Web Assembly Value Encoding writer.
///
/// Writes to the wrapped `W` writer.
pub struct Writer<W> {
    inner: W,
}

impl<W: Write> Writer<W> {
    /// Returns a new Writer for the given [`std::io::Write`].
    pub fn new(w: W) -> Self {
        Self { inner: w }
    }

    /// WAVE-encodes and writes the given [`WasmValue`] to the underlying writer.
    pub fn write_value<V>(&mut self, val: &V) -> Result<(), WriterError>
    where
        V: WasmValue,
    {
        let ty = val.ty();
        match ty.kind() {
            crate::ty::WasmTypeKind::Bool => {
                self.write_str(if val.unwrap_bool() { "true" } else { "false" })
            }
            crate::ty::WasmTypeKind::S8 => self.write_display(val.unwrap_s8()),
            crate::ty::WasmTypeKind::S16 => self.write_display(val.unwrap_s16()),
            crate::ty::WasmTypeKind::S32 => self.write_display(val.unwrap_s32()),
            crate::ty::WasmTypeKind::S64 => self.write_display(val.unwrap_s64()),
            crate::ty::WasmTypeKind::U8 => self.write_display(val.unwrap_u8()),
            crate::ty::WasmTypeKind::U16 => self.write_display(val.unwrap_u16()),
            crate::ty::WasmTypeKind::U32 => self.write_display(val.unwrap_u32()),
            crate::ty::WasmTypeKind::U64 => self.write_display(val.unwrap_u64()),
            crate::ty::WasmTypeKind::Float32 => {
                let f = val.unwrap_float32();
                if f.is_nan() {
                    self.write_str("nan") // Display is "NaN"
                } else {
                    self.write_display(f)
                }
            }
            crate::ty::WasmTypeKind::Float64 => {
                let f = val.unwrap_float64();
                if f.is_nan() {
                    self.write_str("nan") // Display is "NaN"
                } else {
                    self.write_display(f)
                }
            }
            crate::ty::WasmTypeKind::Char => {
                self.write_str("'")?;
                self.write_char(val.unwrap_char())?;
                self.write_str("'")
            }
            crate::ty::WasmTypeKind::String => {
                self.write_str("\"")?;
                for ch in val.unwrap_string().chars() {
                    self.write_char(ch)?;
                }
                self.write_str("\"")
            }
            crate::ty::WasmTypeKind::List => {
                self.write_str("[")?;
                for (idx, val) in val.unwrap_list().enumerate() {
                    if idx != 0 {
                        self.write_str(", ")?;
                    }
                    self.write_value(&*val)?;
                }
                self.write_str("]")
            }
            crate::ty::WasmTypeKind::Record => {
                self.write_str("{")?;
                let mut first = true;
                for (name, val) in val.unwrap_record() {
                    if !matches!(val.ty().kind(), WasmTypeKind::Option)
                        || val.unwrap_option().is_some()
                    {
                        if first {
                            first = false;
                        } else {
                            self.write_str(", ")?;
                        }
                        self.write_str(name)?;
                        self.write_str(": ")?;
                        self.write_value(&*val)?;
                    }
                }
                if first {
                    self.write_str(":")?;
                }
                self.write_str("}")
            }
            crate::ty::WasmTypeKind::Tuple => {
                self.write_str("(")?;
                for (idx, val) in val.unwrap_tuple().enumerate() {
                    if idx != 0 {
                        self.write_str(", ")?;
                    }
                    self.write_value(&*val)?;
                }
                self.write_str(")")
            }
            crate::ty::WasmTypeKind::Variant => {
                let (name, val) = val.unwrap_variant();
                if Keyword::from_label(&name).is_some() {
                    self.write_char('%')?;
                }
                self.write_str(name)?;
                if let Some(val) = val {
                    self.write_str("(")?;
                    self.write_value(&*val)?;
                    self.write_str(")")?;
                }
                Ok(())
            }
            crate::ty::WasmTypeKind::Enum => {
                let case = val.unwrap_enum();
                if Keyword::from_label(&case).is_some() {
                    self.write_char('%')?;
                }
                self.write_str(case)
            }
            crate::ty::WasmTypeKind::Option => match val.unwrap_option() {
                Some(val) => {
                    self.write_str("some(")?;
                    self.write_value(&*val)?;
                    self.write_str(")")
                }
                None => self.write_str("none"),
            },
            crate::ty::WasmTypeKind::Result => {
                let (name, val) = match val.unwrap_result() {
                    Ok(val) => ("ok", val),
                    Err(val) => ("err", val),
                };
                self.write_str(name)?;
                if let Some(val) = val {
                    self.write_str("(")?;
                    self.write_value(&*val)?;
                    self.write_str(")")?;
                }
                Ok(())
            }
            crate::ty::WasmTypeKind::Flags => {
                self.write_str("{")?;
                for (idx, name) in val.unwrap_flags().enumerate() {
                    if idx != 0 {
                        self.write_str(", ")?;
                    }
                    self.write_str(name)?;
                }
                self.write_str("}")?;
                Ok(())
            }
            crate::ty::WasmTypeKind::Unsupported => panic!("unsupported value type"),
        }
    }

    fn write_str(&mut self, s: impl AsRef<str>) -> Result<(), WriterError> {
        self.inner.write_all(s.as_ref().as_bytes())?;
        Ok(())
    }

    fn write_display(&mut self, d: impl std::fmt::Display) -> Result<(), WriterError> {
        write!(self.inner, "{d}")?;
        Ok(())
    }

    fn write_char(&mut self, ch: char) -> Result<(), WriterError> {
        if "\\\"\'\t\r\n".contains(ch) {
            write!(self.inner, "{}", ch.escape_default())?;
        } else if ch.is_control() {
            write!(self.inner, "{}", ch.escape_unicode())?;
        } else {
            write!(self.inner, "{}", ch.escape_debug())?;
        }
        Ok(())
    }
}

impl<W> AsMut<W> for Writer<W> {
    fn as_mut(&mut self) -> &mut W {
        &mut self.inner
    }
}

/// A Writer error.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum WriterError {
    /// An error from the underlying writer
    #[error("write failed: {0}")]
    Io(#[from] std::io::Error),
}
