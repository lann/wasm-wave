use std::borrow::Cow;

use crate::{
    ty::{maybe_unwrap, WasmTypeKind},
    WasmType,
};

#[derive(Clone, PartialEq)]
#[allow(missing_docs)]
pub enum Type {
    Simple(WasmTypeKind),
    List(ListType),
    Record(RecordType),
    Tuple(TupleType),
    Variant(VariantType),
    Enum(EnumType),
    Option(OptionType),
    Result(ResultType),
    Flags(FlagsType),
}

#[allow(missing_docs)]
impl Type {
    pub const BOOL: Self = Self::Simple(WasmTypeKind::Bool);
    pub const S8: Self = Self::Simple(WasmTypeKind::S8);
    pub const S16: Self = Self::Simple(WasmTypeKind::S16);
    pub const S32: Self = Self::Simple(WasmTypeKind::S32);
    pub const S64: Self = Self::Simple(WasmTypeKind::S64);
    pub const U8: Self = Self::Simple(WasmTypeKind::U8);
    pub const U16: Self = Self::Simple(WasmTypeKind::U16);
    pub const U32: Self = Self::Simple(WasmTypeKind::U32);
    pub const U64: Self = Self::Simple(WasmTypeKind::U64);
    pub const FLOAT32: Self = Self::Simple(WasmTypeKind::Float32);
    pub const FLOAT64: Self = Self::Simple(WasmTypeKind::Float64);
    pub const CHAR: Self = Self::Simple(WasmTypeKind::Char);
    pub const STRING: Self = Self::Simple(WasmTypeKind::String);

    /// Returns a list type with the given element type.
    pub fn list(element_type: impl Into<Box<Self>>) -> Self {
        let element = element_type.into();
        Self::List(ListType { element })
    }

    /// Returns a record type with the given field types. Returns None if
    /// `fields` is empty.
    pub fn record<T: Into<Box<str>>>(
        field_types: impl IntoIterator<Item = (T, Self)>,
    ) -> Option<Self> {
        let fields = field_types
            .into_iter()
            .map(|(name, ty)| (name.into(), ty))
            .collect::<Vec<_>>();
        if fields.is_empty() {
            return None;
        }
        Some(Self::Record(RecordType { fields }))
    }

    /// Returns a tuple type with the given element types. Returns None if
    /// `element_types` is empty.
    pub fn tuple(element_types: impl Into<Vec<Self>>) -> Option<Self> {
        let elements = element_types.into();
        if elements.is_empty() {
            return None;
        }
        Some(Self::Tuple(TupleType { elements }))
    }

    /// Returns a variant type with the given case names and optional payloads.
    /// Returns None if `cases` is empty.
    pub fn variant<T: Into<Box<str>>>(
        cases: impl IntoIterator<Item = (T, Option<Self>)>,
    ) -> Option<Self> {
        let cases = cases
            .into_iter()
            .map(|(name, ty)| (name.into(), ty))
            .collect::<Vec<_>>();
        if cases.is_empty() {
            return None;
        }
        Some(Self::Variant(VariantType { cases }))
    }

    /// Returns an enum type with the given case names. Returns None if `cases`
    /// is empty.
    pub fn enum_ty<T: Into<Box<str>>>(cases: impl IntoIterator<Item = T>) -> Option<Self> {
        let cases = cases.into_iter().map(Into::into).collect::<Vec<_>>();
        if cases.is_empty() {
            return None;
        }
        Some(Self::Enum(EnumType { cases }))
    }

    /// Returns an option type with the given "some" type.
    pub fn option(some: Self) -> Self {
        let some = Box::new(some);
        Self::Option(OptionType { some })
    }

    /// Returns a result type with the given optional "ok" and "err" payloads.
    pub fn result(ok: Option<Self>, err: Option<Self>) -> Self {
        let ok = ok.map(Box::new);
        let err = err.map(Box::new);
        Self::Result(ResultType { ok, err })
    }

    /// Returns a flags type with the given flag names. Returns None if `flags`
    /// is empty.
    pub fn flags<T: Into<Box<str>>>(flags: impl IntoIterator<Item = T>) -> Option<Self> {
        let flags = flags.into_iter().map(Into::into).collect::<Vec<_>>();
        if flags.is_empty() {
            return None;
        }
        Some(Self::Flags(FlagsType { flags }))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ListType {
    pub(super) element: Box<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordType {
    pub(super) fields: Vec<(Box<str>, Type)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleType {
    pub(super) elements: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantType {
    pub(super) cases: Vec<(Box<str>, Option<Type>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumType {
    pub(super) cases: Vec<Box<str>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct OptionType {
    pub(super) some: Box<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResultType {
    pub(super) ok: Option<Box<Type>>,
    pub(super) err: Option<Box<Type>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FlagsType {
    pub(super) flags: Vec<Box<str>>,
}

impl WasmType for Type {
    fn kind(&self) -> WasmTypeKind {
        match self {
            Type::Simple(kind) => *kind,
            Type::List(_) => WasmTypeKind::List,
            Type::Record(_) => WasmTypeKind::Record,
            Type::Tuple(_) => WasmTypeKind::Tuple,
            Type::Variant(_) => WasmTypeKind::Variant,
            Type::Enum(_) => WasmTypeKind::Enum,
            Type::Option(_) => WasmTypeKind::Option,
            Type::Result(_) => WasmTypeKind::Result,
            Type::Flags(_) => WasmTypeKind::Flags,
        }
    }

    fn list_element_type(&self) -> Option<Self> {
        let list = maybe_unwrap!(self, Self::List)?.clone();
        Some(*list.element)
    }

    fn record_fields(&self) -> Box<dyn Iterator<Item = (Cow<str>, Self)> + '_> {
        let Self::Record(record) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(
            record
                .fields
                .iter()
                .map(|(name, ty)| (name.as_ref().into(), ty.clone())),
        )
    }

    fn tuple_element_types(&self) -> Box<dyn Iterator<Item = Self> + '_> {
        let Self::Tuple(tuple) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(tuple.elements.iter().cloned())
    }

    fn variant_cases(&self) -> Box<dyn Iterator<Item = (Cow<str>, Option<Self>)> + '_> {
        let Self::Variant(variant) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(
            variant
                .cases
                .iter()
                .map(|(name, ty)| (name.as_ref().into(), ty.clone())),
        )
    }

    fn enum_cases(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        let Self::Enum(enum_) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(enum_.cases.iter().map(|name| name.as_ref().into()))
    }

    fn option_some_type(&self) -> Option<Self> {
        let option = maybe_unwrap!(self, Self::Option)?.clone();
        Some(*option.some)
    }

    fn result_types(&self) -> Option<(Option<Self>, Option<Self>)> {
        let result = maybe_unwrap!(self, Self::Result)?;
        Some((
            result.ok.as_deref().cloned(),
            result.err.as_deref().cloned(),
        ))
    }

    fn flags_names(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        let Self::Flags(flags) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(flags.flags.iter().map(|name| name.as_ref().into()))
    }
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        crate::fmt::TypeDebug(self.clone()).fmt(f)
    }
}
