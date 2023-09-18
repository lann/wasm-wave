use std::fmt::Debug;

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

pub trait Type: Clone + Debug + Sized {
    fn kind(&self) -> Kind;
    fn list_element_type(&self) -> Self {
        unimplemented!()
    }
    fn record_fields(&self) -> Box<dyn Iterator<Item = (&str, Self)> + '_> {
        unimplemented!()
    }
    fn tuple_element_types(&self) -> Box<dyn Iterator<Item = Self> + '_> {
        unimplemented!()
    }
    fn variant_cases(&self) -> Box<dyn Iterator<Item = (&str, Option<Self>)> + '_> {
        unimplemented!()
    }
    fn enum_cases(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        unimplemented!()
    }
    fn option_some_type(&self) -> Self {
        unimplemented!()
    }
    fn result_types(&self) -> (Option<Self>, Option<Self>) {
        unimplemented!()
    }
    fn flags_names(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        unimplemented!()
    }
}
