//! Value enum for WAVE values.
#![allow(missing_docs)]

mod convert;
#[cfg(test)]
mod tests;
mod ty;

#[cfg(feature = "wit")]
mod wit;

#[cfg(feature = "wit")]
pub use wit::resolve_wit_type;

use std::{borrow::Cow, collections::HashMap};

use crate::{
    ty::{maybe_unwrap, Kind},
    val::unwrap_val,
    Type, Val,
};

pub use self::ty::ValueType;
use self::ty::{
    EnumType, FlagsType, ListType, OptionType, RecordType, ResultType, TupleType, VariantType,
};

/// A Value is a WAVE value.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Bool(bool),
    S8(i8),
    U8(u8),
    S16(i16),
    U16(u16),
    S32(i32),
    U32(u32),
    S64(i64),
    U64(u64),
    Float32(f32),
    Float64(f64),
    Char(char),
    String(Box<str>),
    List(List),
    Record(Record),
    Tuple(Tuple),
    Variant(Variant),
    Enum(Enum),
    Option(OptionValue),
    Result(ResultValue),
    Flags(Flags),
}

#[derive(Debug, Clone, PartialEq)]
pub struct List {
    ty: ListType,
    elements: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Record {
    ty: RecordType,
    fields: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Tuple {
    ty: TupleType,
    elements: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    ty: VariantType,
    case: usize,
    payload: Option<Box<Value>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Enum {
    ty: EnumType,
    case: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct OptionValue {
    ty: OptionType,
    value: Option<Box<Value>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResultValue {
    ty: ResultType,
    value: Result<Option<Box<Value>>, Option<Box<Value>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Flags {
    ty: FlagsType,
    flags: Vec<usize>,
}

macro_rules! impl_primitives {
    ($Self:ident, $(($case:ident, $ty:ty, $make:ident, $unwrap:ident)),*) => {
        $(
            fn $make(val: $ty) -> $Self {
                $Self::$case(val)
            }

            fn $unwrap(&self) -> $ty {
                *unwrap_val!(self, $Self::$case, stringify!($case))
            }
        )*
    };
}

impl Val for Value {
    type Type = ValueType;

    type Error = ValueError;

    fn ty(&self) -> Self::Type {
        match self {
            Self::Bool(_) => ValueType::Simple(Kind::Bool),
            Self::S8(_) => ValueType::Simple(Kind::S8),
            Self::S16(_) => ValueType::Simple(Kind::S16),
            Self::S32(_) => ValueType::Simple(Kind::S32),
            Self::S64(_) => ValueType::Simple(Kind::S64),
            Self::U8(_) => ValueType::Simple(Kind::U8),
            Self::U16(_) => ValueType::Simple(Kind::U16),
            Self::U32(_) => ValueType::Simple(Kind::U32),
            Self::U64(_) => ValueType::Simple(Kind::U64),
            Self::Float32(_) => ValueType::Simple(Kind::Float32),
            Self::Float64(_) => ValueType::Simple(Kind::Float64),
            Self::Char(_) => ValueType::Simple(Kind::Char),
            Self::String(_) => ValueType::Simple(Kind::String),
            Self::List(inner) => ValueType::List(inner.ty.clone()),
            Self::Record(inner) => ValueType::Record(inner.ty.clone()),
            Self::Tuple(inner) => ValueType::Tuple(inner.ty.clone()),
            Self::Variant(inner) => ValueType::Variant(inner.ty.clone()),
            Self::Enum(inner) => ValueType::Enum(inner.ty.clone()),
            Self::Option(inner) => ValueType::Option(inner.ty.clone()),
            Self::Result(inner) => ValueType::Result(inner.ty.clone()),
            Self::Flags(inner) => ValueType::Flags(inner.ty.clone()),
        }
    }

    impl_primitives!(
        Self,
        (Bool, bool, make_bool, unwrap_bool),
        (S8, i8, make_s8, unwrap_s8),
        (S16, i16, make_s16, unwrap_s16),
        (S32, i32, make_s32, unwrap_s32),
        (S64, i64, make_s64, unwrap_s64),
        (U8, u8, make_u8, unwrap_u8),
        (U16, u16, make_u16, unwrap_u16),
        (U32, u32, make_u32, unwrap_u32),
        (U64, u64, make_u64, unwrap_u64),
        (Float32, f32, make_float32, unwrap_float32),
        (Float64, f64, make_float64, unwrap_float64),
        (Char, char, make_char, unwrap_char)
    );

    fn make_string(val: std::borrow::Cow<str>) -> Self {
        Self::String(val.into())
    }

    fn make_list(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, Self::Error> {
        let element_type = ty
            .list_element_type()
            .ok_or_else(|| ValueError::InvalidType(format!("{ty:?} is not a valid list type")))?;
        let elements = vals
            .into_iter()
            .map(|v| check_type(&element_type, v))
            .collect::<Result<_, ValueError>>()?;
        let ty = maybe_unwrap!(ty, ValueType::List).unwrap().clone();
        Ok(Self::List(List { ty, elements }))
    }

    fn make_record<'a>(
        ty: &Self::Type,
        fields: impl IntoIterator<Item = (&'a str, Self)>,
    ) -> Result<Self, Self::Error> {
        let mut field_vals: HashMap<_, _> = fields.into_iter().collect();
        let mut fields = Vec::with_capacity(field_vals.len());
        for (name, ty) in ty.record_fields() {
            let val = field_vals
                .remove(&*name)
                .ok_or_else(|| ValueError::MissingField(name.into()))?;
            fields.push(check_type(&ty, val)?);
        }
        if fields.is_empty() {
            return Err(ValueError::InvalidType(format!(
                "{ty:?} is not a valid record type"
            )));
        }
        if let Some(unknown) = field_vals.into_keys().next() {
            return Err(ValueError::MissingField(unknown.into()));
        }
        let ty = maybe_unwrap!(ty, ValueType::Record).unwrap().clone();
        Ok(Self::Record(Record { ty, fields }))
    }

    fn make_tuple(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, Self::Error> {
        let types = ty.tuple_element_types().collect::<Vec<_>>();
        let elements = vals
            .into_iter()
            .enumerate()
            .map(|(idx, val)| {
                let ty = types
                    .get(idx)
                    .ok_or_else(|| ValueError::InvalidValue("too many tuple values".into()))?;
                check_type(ty, val)
            })
            .collect::<Result<Vec<_>, ValueError>>()?;
        if types.len() != elements.len() {
            return Err(ValueError::InvalidValue(format!(
                "tuple needs {} values; got {}",
                types.len(),
                elements.len()
            )));
        }
        let ty = maybe_unwrap!(ty, ValueType::Tuple).unwrap().clone();
        Ok(Self::Tuple(Tuple { ty, elements }))
    }

    fn make_variant(ty: &Self::Type, case: &str, val: Option<Self>) -> Result<Self, Self::Error> {
        let (case, payload_type) = ty
            .variant_cases()
            .enumerate()
            .find_map(|(idx, (name, ty))| (name == case).then_some((idx, ty)))
            .ok_or_else(|| ValueError::InvalidValue(format!("unknown case `{case}` for {ty:?}")))?;
        let payload = check_option_type(&payload_type, val)?;
        let ty = maybe_unwrap!(ty, ValueType::Variant).unwrap().clone();
        Ok(Self::Variant(Variant { ty, case, payload }))
    }

    fn make_enum(ty: &Self::Type, case: &str) -> Result<Self, Self::Error> {
        let case = ty
            .enum_cases()
            .position(|name| name == case)
            .ok_or_else(|| ValueError::InvalidValue(format!("unknown case `{case}` for {ty:?}")))?;
        let ty = maybe_unwrap!(ty, ValueType::Enum).unwrap().clone();
        Ok(Self::Enum(Enum { ty, case }))
    }

    fn make_option(ty: &Self::Type, val: Option<Self>) -> Result<Self, Self::Error> {
        let some_type = ty
            .option_some_type()
            .ok_or_else(|| ValueError::InvalidType(format!("{ty:?} is not an option type")))?;
        let value = val
            .map(|val| Ok(Box::new(check_type(&some_type, val)?)))
            .transpose()?;
        let ty = maybe_unwrap!(ty, ValueType::Option).unwrap().clone();
        Ok(Self::Option(OptionValue { ty, value }))
    }

    fn make_result(
        ty: &Self::Type,
        val: Result<Option<Self>, Option<Self>>,
    ) -> Result<Self, Self::Error> {
        let (ok_type, err_type) = ty
            .result_types()
            .ok_or_else(|| ValueError::InvalidType(format!("{ty:?} is not a result type")))?;
        let value = match val {
            Ok(ok) => Ok(check_option_type(&ok_type, ok)?),
            Err(err) => Err(check_option_type(&err_type, err)?),
        };
        let ty = maybe_unwrap!(ty, ValueType::Result).unwrap().clone();
        Ok(Self::Result(ResultValue { ty, value }))
    }

    fn make_flags<'a>(
        ty: &Self::Type,
        names: impl IntoIterator<Item = &'a str>,
    ) -> Result<Self, Self::Error> {
        let flag_names = ty.flags_names().collect::<Vec<_>>();
        let flags = names
            .into_iter()
            .map(|name| {
                flag_names
                    .iter()
                    .position(|flag| flag == name)
                    .ok_or_else(|| ValueError::InvalidValue(format!("unknown flag `{name}`")))
            })
            .collect::<Result<Vec<_>, ValueError>>()?;
        let ty = maybe_unwrap!(ty, ValueType::Flags).unwrap().clone();
        Ok(Self::Flags(Flags { ty, flags }))
    }

    fn unwrap_string(&self) -> std::borrow::Cow<str> {
        unwrap_val!(self, Self::String, "string").as_ref().into()
    }
    fn unwrap_list(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        let list = unwrap_val!(self, Self::List, "list");
        Box::new(list.elements.iter().map(cow))
    }
    fn unwrap_record(&self) -> Box<dyn Iterator<Item = (Cow<str>, Cow<Self>)> + '_> {
        let record = unwrap_val!(self, Self::Record, "record");
        Box::new(
            record
                .ty
                .fields
                .iter()
                .map(|(name, _)| cow(name.as_ref()))
                .zip(record.fields.iter().map(cow)),
        )
    }
    fn unwrap_tuple(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        let tuple = unwrap_val!(self, Self::Tuple, "tuple");
        Box::new(tuple.elements.iter().map(cow))
    }
    fn unwrap_variant(&self) -> (Cow<str>, Option<Cow<Self>>) {
        let variant = unwrap_val!(self, Self::Variant, "variant");
        let (ref name, _) = variant.ty.cases[variant.case];
        (cow(name.as_ref()), variant.payload.as_deref().map(cow))
    }
    fn unwrap_enum(&self) -> Cow<str> {
        let enum_ = unwrap_val!(self, Self::Enum, "enum");
        cow(enum_.ty.cases[enum_.case].as_ref())
    }
    fn unwrap_option(&self) -> Option<Cow<Self>> {
        unwrap_val!(self, Self::Option, "option")
            .value
            .as_ref()
            .map(|v| cow(v.as_ref()))
    }
    fn unwrap_result(&self) -> Result<Option<Cow<Self>>, Option<Cow<Self>>> {
        match &unwrap_val!(self, Self::Result, "result").value {
            Ok(val) => Ok(val.as_deref().map(cow)),
            Err(val) => Err(val.as_deref().map(cow)),
        }
    }
    fn unwrap_flags(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        let flags = unwrap_val!(self, Self::Flags, "flags");
        Box::new(
            flags
                .flags
                .iter()
                .map(|idx| cow(flags.ty.flags[*idx].as_ref())),
        )
    }
}

fn cow<T: ToOwned + ?Sized>(t: &T) -> Cow<T> {
    Cow::Borrowed(t)
}

fn check_type(expected: &ValueType, val: Value) -> Result<Value, ValueError> {
    let got = val.ty();
    if &got != expected {
        return Err(ValueError::InvalidType(format!(
            "expected {expected:?}, got {got:?}"
        )));
    }
    Ok(val)
}

fn check_option_type(
    expected: &Option<ValueType>,
    val: Option<Value>,
) -> Result<Option<Box<Value>>, ValueError> {
    match (expected, val) {
        (Some(ty), Some(val)) => Ok(Some(Box::new(check_type(ty, val)?))),
        (None, None) => Ok(None),
        (ty, val) => Err(ValueError::InvalidValue(format!(
            "invalid payload {val:?}; expected {ty:?}"
        ))),
    }
}

/// Value errors.
#[derive(Debug, thiserror::Error)]
pub enum ValueError {
    #[error("missing field `{0}`")]
    MissingField(Box<str>),

    #[error("unknown field `{0}`")]
    UnknownField(Box<str>),

    #[error("invalid type: {0}")]
    InvalidType(String),

    #[error("invalid value: {0}")]
    InvalidValue(String),
}
