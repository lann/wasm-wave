//! WAVE encoder.

use std::{borrow::Borrow, fmt::Debug, io::Write};

use thiserror::Error;

use crate::{
    ty::{Kind, Type},
    val::Val,
};

/// A WAVE writer (encoder).
pub struct Writer<W> {
    inner: W,
}

impl<W: Write> Writer<W> {
    /// Returns a new Writer for the given [`std::io::Write`].
    pub fn new(w: W) -> Self {
        Self { inner: w }
    }

    /// WAVE-encodes and writes the given [`Val`] to the underlying writer.
    pub fn write_value<V>(&mut self, val: &V) -> Result<(), Error>
    where
        V: Val,
        V::Type: Debug,
    {
        let val = val.borrow();
        let ty = val.ty();
        match ty.kind() {
            crate::ty::Kind::Bool => {
                self.write_str(if val.unwrap_bool() { "true" } else { "false" })
            }
            crate::ty::Kind::S8 => self.write_display(val.unwrap_s8()),
            crate::ty::Kind::S16 => self.write_display(val.unwrap_s16()),
            crate::ty::Kind::S32 => self.write_display(val.unwrap_s32()),
            crate::ty::Kind::S64 => self.write_display(val.unwrap_s64()),
            crate::ty::Kind::U8 => self.write_display(val.unwrap_u8()),
            crate::ty::Kind::U16 => self.write_display(val.unwrap_u16()),
            crate::ty::Kind::U32 => self.write_display(val.unwrap_u32()),
            crate::ty::Kind::U64 => self.write_display(val.unwrap_u64()),
            crate::ty::Kind::Float32 => {
                let f = val.unwrap_float32();
                if f.is_nan() {
                    self.write_str("nan") // Display is "NaN"
                } else {
                    self.write_display(f)
                }
            }
            crate::ty::Kind::Float64 => {
                let f = val.unwrap_float64();
                if f.is_nan() {
                    self.write_str("nan") // Display is "NaN"
                } else {
                    self.write_display(f)
                }
            }
            crate::ty::Kind::Char => {
                self.write_str("'")?;
                self.write_char(val.unwrap_char())?;
                self.write_str("'")
            }
            crate::ty::Kind::String => {
                self.write_str("\"")?;
                for ch in val.unwrap_string().chars() {
                    self.write_char(ch)?;
                }
                self.write_str("\"")
            }
            crate::ty::Kind::List => {
                self.write_str("[")?;
                for (idx, val) in val.unwrap_list().enumerate() {
                    if idx != 0 {
                        self.write_str(", ")?;
                    }
                    self.write_value(&*val)?;
                }
                self.write_str("]")
            }
            crate::ty::Kind::Record => {
                self.write_str("{")?;
                let mut first = true;
                for (name, val) in val.unwrap_record() {
                    if !matches!(val.ty().kind(), Kind::Option) || val.unwrap_option().is_some() {
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
                self.write_str("}")
            }
            crate::ty::Kind::Tuple => {
                self.write_str("(")?;
                for (idx, val) in val.unwrap_tuple().enumerate() {
                    if idx != 0 {
                        self.write_str(", ")?;
                    }
                    self.write_value(&*val)?;
                }
                self.write_str(")")
            }
            crate::ty::Kind::Variant => {
                let (name, val) = val.unwrap_variant();
                self.write_str(name)?;
                if let Some(val) = val {
                    self.write_str("(")?;
                    self.write_value(&*val)?;
                    self.write_str(")")?;
                }
                Ok(())
            }
            crate::ty::Kind::Enum => self.write_str(val.unwrap_enum()),
            crate::ty::Kind::Option => match val.unwrap_option() {
                Some(val) => {
                    self.write_str("some(")?;
                    self.write_value(&*val)?;
                    self.write_str(")")
                }
                None => self.write_str("none"),
            },
            crate::ty::Kind::Result => {
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
            crate::ty::Kind::Flags => {
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
            crate::ty::Kind::Unsupported => panic!("unsupported value type {ty:?}"),
        }
    }

    fn write_str(&mut self, s: impl AsRef<str>) -> Result<(), Error> {
        self.inner.write_all(s.as_ref().as_bytes())?;
        Ok(())
    }

    fn write_display(&mut self, d: impl std::fmt::Display) -> Result<(), Error> {
        write!(self.inner, "{d}")?;
        Ok(())
    }

    fn write_char(&mut self, ch: char) -> Result<(), Error> {
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

/// A Writer error.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Error {
    /// An error from the underlying writer
    #[error("write failed: {0}")]
    Io(#[from] std::io::Error),
}
