use std::borrow::Cow;

use crate::{
    fmt::{DisplayType, DisplayValue},
    ty::WasmType,
    WasmTypeKind,
};

/// The WasmValue trait may be implemented to represent values to be
/// (de)serialized with WAVE, notably [`value::Value`](crate::value::Value)
/// and [`wasmtime::component::Val`].
///
/// The `make_*` and `unwrap_*` methods should be called only for corresponding
/// [`WasmTypeKind`](crate::WasmTypeKind)s.
#[allow(unused_variables)]
pub trait WasmValue: Clone + Sized {
    /// A type representing types of these values.
    type Type: WasmType;

    /// The type of this value.
    fn ty(&self) -> Self::Type;

    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_bool(val: bool) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_s8(val: i8) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_s16(val: i16) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_s32(val: i32) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_s64(val: i64) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_u8(val: u8) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_u16(val: u16) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_u32(val: u32) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_u64(val: u64) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    ///
    /// The Rust `f32` type has many distinct NaN bitpatterns, however the
    /// component-model `float32` type only has a single NaN value, so this
    /// function does not preserve NaN bitpatterns.
    ///
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_float32(val: f32) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    ///
    /// The Rust `f64` type has many distinct NaN bitpatterns, however the
    /// component-model `float64` type only has a single NaN value, so this
    /// function does not preserve NaN bitpatterns.
    ///
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_float64(val: f64) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_char(val: char) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_string(val: Cow<str>) -> Self {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_list(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, WasmValueError> {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    ///
    /// The fields provided by `fields` are not necessarily sorted; the callee
    /// should perform sorting itself if needed.
    ///
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_record<'a>(
        ty: &Self::Type,
        fields: impl IntoIterator<Item = (&'a str, Self)>,
    ) -> Result<Self, WasmValueError> {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_tuple(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, WasmValueError> {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_variant(
        ty: &Self::Type,
        case: &str,
        val: Option<Self>,
    ) -> Result<Self, WasmValueError> {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_enum(ty: &Self::Type, case: &str) -> Result<Self, WasmValueError> {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_option(ty: &Self::Type, val: Option<Self>) -> Result<Self, WasmValueError> {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_result(
        ty: &Self::Type,
        val: Result<Option<Self>, Option<Self>>,
    ) -> Result<Self, WasmValueError> {
        unimplemented!()
    }
    /// Returns a new WasmValue of the given type.
    ///
    /// The strings provided by `names` are not necessarily sorted; the callee
    /// should perform sorting itself if needed.
    ///
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn make_flags<'a>(
        ty: &Self::Type,
        names: impl IntoIterator<Item = &'a str>,
    ) -> Result<Self, WasmValueError> {
        unimplemented!()
    }

    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_bool(&self) -> bool {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_s8(&self) -> i8 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_s16(&self) -> i16 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_s32(&self) -> i32 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_s64(&self) -> i64 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_u8(&self) -> u8 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_u16(&self) -> u16 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_u32(&self) -> u32 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_u64(&self) -> u64 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    ///
    /// The Rust `f32` type has many distinct NaN bitpatterns, however the
    /// component-model `float64` type only has a single NaN value, so this
    /// function does not preserve NaN bitpatterns.
    ///
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_float32(&self) -> f32 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    ///
    /// The Rust `f64` type has many distinct NaN bitpatterns, however the
    /// component-model `float64` type only has a single NaN value, so this
    /// function does not preserve NaN bitpatterns.
    ///
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_float64(&self) -> f64 {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_char(&self) -> char {
        unimplemented!()
    }
    /// Returns the underlying value of the WasmValue, panicing if it's the wrong type.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_string(&self) -> Cow<str> {
        unimplemented!()
    }
    /// Returns an iterator of the element Vals of the list.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_list(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the field names and Vals of the record.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_record(&self) -> Box<dyn Iterator<Item = (Cow<str>, Cow<Self>)> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the field Vals of the tuple.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_tuple(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        unimplemented!()
    }
    /// Returns the variant case name and optional payload WasmValue of the variant.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_variant(&self) -> (Cow<str>, Option<Cow<Self>>) {
        unimplemented!()
    }
    /// Returns the case name of the enum.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_enum(&self) -> Cow<str> {
        unimplemented!()
    }
    /// Returns the optional WasmValue.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_option(&self) -> Option<Cow<Self>> {
        unimplemented!()
    }
    /// Returns Ok(_) or Err(_) with the optional payload WasmValue.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_result(&self) -> Result<Option<Cow<Self>>, Option<Cow<Self>>> {
        unimplemented!()
    }
    /// Returns an iterator of the names of the flags WasmValue.
    /// # Panics
    /// Panics if `self` is not of the right type.
    fn unwrap_flags(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        unimplemented!()
    }
}

/// Returns an error if the given [`WasmType`] is not of the given [`WasmTypeKind`].
pub fn ensure_type_kind(ty: &impl WasmType, kind: WasmTypeKind) -> Result<(), WasmValueError> {
    if ty.kind() == kind {
        Ok(())
    } else {
        Err(WasmValueError::WrongTypeKind {
            ty: DisplayType(ty).to_string(),
            kind,
        })
    }
}

/// An error from creating a [`WasmValue`].
#[derive(Debug)]
pub enum WasmValueError {
    MissingField(String),
    MissingPayload(String),
    UnexpectedPayload(String),
    UnknownCase(String),
    UnknownField(String),
    UnsupportedType(String),
    WrongNumberOfTupleValues { want: usize, got: usize },
    WrongTypeKind { kind: WasmTypeKind, ty: String },
    WrongValueType { ty: String, val: String },
    Other(String),
}

impl WasmValueError {
    pub(crate) fn wrong_value_type(ty: &impl WasmType, val: &impl WasmValue) -> Self {
        Self::WrongValueType {
            ty: DisplayType(ty).to_string(),
            val: DisplayValue(val).to_string(),
        }
    }

    pub(crate) fn other(msg: impl std::fmt::Display) -> Self {
        Self::Other(msg.to_string())
    }
}

impl std::fmt::Display for WasmValueError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingField(name) => {
                write!(f, "missing field {name:?}")
            }
            Self::MissingPayload(name) => write!(f, "missing payload for {name:?} case"),
            Self::UnexpectedPayload(name) => write!(f, "unexpected payload for {name:?} case"),
            Self::UnknownCase(name) => write!(f, "unknown case {name:?}"),
            Self::UnknownField(name) => write!(f, "unknown field {name:?}"),
            Self::UnsupportedType(ty) => write!(f, "unsupported type {ty}"),
            Self::WrongNumberOfTupleValues { want, got } => {
                write!(f, "expected {want} tuple elements; got {got}")
            }
            Self::WrongTypeKind { kind, ty } => {
                write!(f, "expected a {kind}; got {ty}")
            }
            Self::WrongValueType { ty, val } => {
                write!(f, "expected a {ty}; got {val}")
            }
            Self::Other(msg) => write!(f, "{msg}"),
        }
    }
}

macro_rules! unwrap_val {
    ($val:expr, $case:path, $name:expr) => {
        match $val {
            $case(v) => v,
            _ => panic!("called unwrap_{name} on non-{name} value", name = $name),
        }
    };
}
pub(crate) use unwrap_val;
