use std::fmt::Debug;

/// The kind of a [`Type`]. These correspond to the value types defined by the
/// [Component Model design](https://github.com/WebAssembly/component-model/blob/673d5c43c3cc0f4aeb8996a5c0931af623f16808/design/mvp/WIT.md).
#[derive(Debug, PartialEq)]
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
    Unsupported,
}

/// The Type trait may be implemented to represent types to be
/// (de)serialized with WAVE, notably [`wasmtime::component::Type`].
///
/// The `Self`-returning methods should be called only for corresponding
/// [`Kind`]s.
pub trait Type: Clone + Debug + Sized {
    /// Returns the [`Kind`] of this Type.
    fn kind(&self) -> Kind;

    /// Returns the list element Type.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn list_element_type(&self) -> Self {
        unimplemented!()
    }
    /// Returns an iterator of the record's field names and Types.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn record_fields(&self) -> Box<dyn Iterator<Item = (&str, Self)> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the tuple's field Types.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn tuple_element_types(&self) -> Box<dyn Iterator<Item = Self> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the variant's case names and optional payload Types.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn variant_cases(&self) -> Box<dyn Iterator<Item = (&str, Option<Self>)> + '_> {
        unimplemented!()
    }
    /// Returns an iterator of the enum's case names.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn enum_cases(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        unimplemented!()
    }
    /// Returns the option's "some" Type.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn option_some_type(&self) -> Self {
        unimplemented!()
    }
    /// Returns the result's optional "ok" and "err" Types.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn result_types(&self) -> (Option<Self>, Option<Self>) {
        unimplemented!()
    }
    /// Returns an iterator of the flags' names.
    /// # Panics
    /// Panics if `self` is not of the right kind.
    fn flags_names(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        unimplemented!()
    }
}
