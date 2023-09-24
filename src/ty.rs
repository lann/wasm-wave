use std::{borrow::Cow, fmt::Debug};

/// The kind of a [`Type`]. These correspond to the value types defined by the
/// [Component Model design](https://github.com/WebAssembly/component-model/blob/673d5c43c3cc0f4aeb8996a5c0931af623f16808/design/mvp/WIT.md).
#[derive(Clone, Copy, Debug, PartialEq)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum Kind {
    Bool,
    S8,
    S16,
    S32,
    S64,
    U8,
    U16,
    U32,
    U64,
    Float32,
    Float64,
    Char,
    String,
    List,
    Record,
    Tuple,
    Variant,
    Enum,
    Option,
    Result,
    Flags,
    #[doc(hidden)]
    Unsupported,
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Kind::Bool => "bool",
            Kind::S8 => "s8",
            Kind::S16 => "s16",
            Kind::S32 => "s32",
            Kind::S64 => "s64",
            Kind::U8 => "u8",
            Kind::U16 => "u16",
            Kind::U32 => "u32",
            Kind::U64 => "u64",
            Kind::Float32 => "float32",
            Kind::Float64 => "float64",
            Kind::Char => "char",
            Kind::String => "string",
            Kind::List => "list",
            Kind::Record => "record",
            Kind::Tuple => "tuple",
            Kind::Variant => "variant",
            Kind::Enum => "enum",
            Kind::Option => "option",
            Kind::Result => "result",
            Kind::Flags => "flags",
            Kind::Unsupported => "<<UNSUPPORTED>>",
        })
    }
}

/// The Type trait may be implemented to represent types to be
/// (de)serialized with WAVE, notably [`wasmtime::component::Type`].
///
/// The `Self`-returning methods should be called only for corresponding
/// [`Kind`]s.
pub trait Type: Clone + Sized {
    /// Returns the [`Kind`] of this Type.
    fn kind(&self) -> Kind;

    /// Returns the list element Type or None if `self` is not a list type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn list_element_type(&self) -> Option<Self> {
        unimplemented!()
    }
    /// Returns an iterator of the record's field names and Types. The
    /// iterator will be empty iff `self` is not a record type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn record_fields(&self) -> Box<dyn Iterator<Item = (Cow<str>, Self)> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the tuple's field Types. The iterator will be
    /// empty iff `self` is not a tuple type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn tuple_element_types(&self) -> Box<dyn Iterator<Item = Self> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the variant's case names and optional payload
    /// Types. The iterator will be empty iff `self` is not a tuple type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn variant_cases(&self) -> Box<dyn Iterator<Item = (Cow<str>, Option<Self>)> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the enum's case names. The iterator will be
    /// empty iff `self` is not an enum type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn enum_cases(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        unimplemented!()
    }
    /// Returns the option's "some" Type or None if `self` is not an option type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn option_some_type(&self) -> Option<Self> {
        unimplemented!()
    }
    /// Returns the result's optional "ok" and "err" Types or None if `self`
    /// is not a result type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn result_types(&self) -> Option<(Option<Self>, Option<Self>)> {
        unimplemented!()
    }
    /// Returns an iterator of the flags' names. The iterator will be empty iff
    /// `self` is not a flags type.
    /// # Panics
    /// Panics if the type is not implemented (the trait default).
    fn flags_names(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        unimplemented!()
    }
}

macro_rules! maybe_unwrap {
    ($ty:ident, $case:path) => {
        match $ty {
            $case(v) => Some(v),
            _ => None,
        }
    };
}

pub(crate) use maybe_unwrap;
