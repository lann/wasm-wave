//! Value enum for WAVE values.

mod convert;
#[cfg(test)]
mod tests;
mod ty;

mod func;
#[cfg(feature = "wit")]
mod wit;

#[cfg(feature = "wit")]
pub use wit::{resolve_wit_func_type, resolve_wit_type};

use std::{borrow::Cow, collections::HashMap, sync::Arc};

use self::ty::{
    EnumType, FlagsType, ListType, OptionType, RecordType, ResultType, TupleType, TypeEnum,
    VariantType,
};
use crate::val::{ensure_type_kind, WasmValueError};
use crate::{canonicalize_nan32, canonicalize_nan64, WasmTypeKind};
use crate::{ty::maybe_unwrap, val::unwrap_val, WasmType, WasmValue};

pub use func::FuncType;
pub use ty::Type;

/// A Value is a WAVE value, and implements [`WasmValue`].
#[derive(Debug, Clone, PartialEq)]
pub struct Value(ValueEnum);

#[derive(Debug, Clone, PartialEq)]
pub(super) enum ValueEnum {
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
#[doc(hidden)]
pub struct List {
    ty: Arc<ListType>,
    elements: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
#[doc(hidden)]
pub struct Record {
    ty: Arc<RecordType>,
    fields: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
#[doc(hidden)]
pub struct Tuple {
    ty: Arc<TupleType>,
    elements: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
#[doc(hidden)]
pub struct Variant {
    ty: Arc<VariantType>,
    case: usize,
    payload: Option<Box<Value>>,
}

#[derive(Debug, Clone, PartialEq)]
#[doc(hidden)]
pub struct Enum {
    ty: Arc<EnumType>,
    case: usize,
}

#[derive(Debug, Clone, PartialEq)]
#[doc(hidden)]
pub struct OptionValue {
    ty: Arc<OptionType>,
    value: Option<Box<Value>>,
}

#[derive(Debug, Clone, PartialEq)]
#[doc(hidden)]
pub struct ResultValue {
    ty: Arc<ResultType>,
    value: Result<Option<Box<Value>>, Option<Box<Value>>>,
}

#[derive(Debug, Clone, PartialEq)]
#[doc(hidden)]
pub struct Flags {
    ty: Arc<FlagsType>,
    flags: Vec<usize>,
}

macro_rules! impl_primitives {
    ($Self:ident, $(($case:ident, $ty:ty, $make:ident, $unwrap:ident)),*) => {
        $(
            fn $make(val: $ty) -> $Self {
                $Self(ValueEnum::$case(val))
            }

            fn $unwrap(&self) -> $ty {
                *unwrap_val!(&self.0, ValueEnum::$case, stringify!($case))
            }
        )*
    };
}

impl WasmValue for Value {
    type Type = Type;

    fn ty(&self) -> Self::Type {
        match &self.0 {
            ValueEnum::Bool(_) => Type::BOOL,
            ValueEnum::S8(_) => Type::S8,
            ValueEnum::S16(_) => Type::S16,
            ValueEnum::S32(_) => Type::S32,
            ValueEnum::S64(_) => Type::S64,
            ValueEnum::U8(_) => Type::U8,
            ValueEnum::U16(_) => Type::U16,
            ValueEnum::U32(_) => Type::U32,
            ValueEnum::U64(_) => Type::U64,
            ValueEnum::Float32(_) => Type::FLOAT32,
            ValueEnum::Float64(_) => Type::FLOAT64,
            ValueEnum::Char(_) => Type::CHAR,
            ValueEnum::String(_) => Type::STRING,
            ValueEnum::List(inner) => Type(TypeEnum::List(inner.ty.clone())),
            ValueEnum::Record(inner) => Type(TypeEnum::Record(inner.ty.clone())),
            ValueEnum::Tuple(inner) => Type(TypeEnum::Tuple(inner.ty.clone())),
            ValueEnum::Variant(inner) => Type(TypeEnum::Variant(inner.ty.clone())),
            ValueEnum::Enum(inner) => Type(TypeEnum::Enum(inner.ty.clone())),
            ValueEnum::Option(inner) => Type(TypeEnum::Option(inner.ty.clone())),
            ValueEnum::Result(inner) => Type(TypeEnum::Result(inner.ty.clone())),
            ValueEnum::Flags(inner) => Type(TypeEnum::Flags(inner.ty.clone())),
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
        (Char, char, make_char, unwrap_char)
    );

    fn make_float32(val: f32) -> Self {
        let val = canonicalize_nan32(val);
        Self(ValueEnum::Float32(val))
    }

    fn make_float64(val: f64) -> Self {
        let val = canonicalize_nan64(val);
        Self(ValueEnum::Float64(val))
    }

    fn make_string(val: std::borrow::Cow<str>) -> Self {
        Self(ValueEnum::String(val.into()))
    }

    fn make_list(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::List)?;
        let element_type = ty.list_element_type().unwrap();
        let elements = vals
            .into_iter()
            .map(|v| check_type(&element_type, v))
            .collect::<Result<_, _>>()?;
        let ty = maybe_unwrap!(&ty.0, TypeEnum::List).unwrap().clone();
        Ok(Self(ValueEnum::List(List { ty, elements })))
    }

    fn make_record<'a>(
        ty: &Self::Type,
        fields: impl IntoIterator<Item = (&'a str, Self)>,
    ) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::Record)?;
        let mut field_vals: HashMap<_, _> = fields.into_iter().collect();
        let mut fields = Vec::with_capacity(field_vals.len());
        for (name, ty) in ty.record_fields() {
            let val = field_vals
                .remove(&*name)
                .ok_or_else(|| WasmValueError::MissingField(name.into()))?;
            fields.push(check_type(&ty, val)?);
        }
        if let Some(unknown) = field_vals.into_keys().next() {
            return Err(WasmValueError::UnknownField(unknown.into()));
        }
        let ty = maybe_unwrap!(&ty.0, TypeEnum::Record).unwrap().clone();
        Ok(Self(ValueEnum::Record(Record { ty, fields })))
    }

    fn make_tuple(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::Tuple)?;
        let types = ty.tuple_element_types().collect::<Vec<_>>();
        let elements = Vec::from_iter(vals);
        if types.len() != elements.len() {
            return Err(WasmValueError::WrongNumberOfTupleValues {
                want: types.len(),
                got: elements.len(),
            });
        }
        for (ty, val) in types.iter().zip(&elements) {
            if &val.ty() != ty {
                return Err(WasmValueError::wrong_value_type(&val.ty(), val));
            }
        }
        let ty = maybe_unwrap!(&ty.0, TypeEnum::Tuple).unwrap().clone();
        Ok(Self(ValueEnum::Tuple(Tuple { ty, elements })))
    }

    fn make_variant(
        ty: &Self::Type,
        case_name: &str,
        val: Option<Self>,
    ) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::Variant)?;
        let (case, payload_type) = ty
            .variant_cases()
            .enumerate()
            .find_map(|(idx, (name, ty))| (name == case_name).then_some((idx, ty)))
            .ok_or_else(|| WasmValueError::UnknownCase(case_name.into()))?;
        let payload = check_payload_type(case_name, &payload_type, val)?;
        let ty = maybe_unwrap!(&ty.0, TypeEnum::Variant).unwrap().clone();
        Ok(Self(ValueEnum::Variant(Variant { ty, case, payload })))
    }

    fn make_enum(ty: &Self::Type, case: &str) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::Enum)?;
        let case = ty
            .enum_cases()
            .position(|name| name == case)
            .ok_or_else(|| WasmValueError::UnknownCase(case.into()))?;
        let ty = maybe_unwrap!(&ty.0, TypeEnum::Enum).unwrap().clone();
        Ok(Self(ValueEnum::Enum(Enum { ty, case })))
    }

    fn make_option(ty: &Self::Type, val: Option<Self>) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::Option)?;
        let value = match val {
            Some(val) => Some(Box::new(check_type(&ty.option_some_type().unwrap(), val)?)),
            None => None,
        };
        let ty = maybe_unwrap!(&ty.0, TypeEnum::Option).unwrap().clone();
        Ok(Self(ValueEnum::Option(OptionValue { ty, value })))
    }

    fn make_result(
        ty: &Self::Type,
        val: Result<Option<Self>, Option<Self>>,
    ) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::Result)?;
        let (ok_type, err_type) = ty.result_types().unwrap();
        let value = match val {
            Ok(ok) => Ok(check_payload_type("ok", &ok_type, ok)?),
            Err(err) => Err(check_payload_type("err", &err_type, err)?),
        };
        let ty = maybe_unwrap!(&ty.0, TypeEnum::Result).unwrap().clone();
        Ok(Self(ValueEnum::Result(ResultValue { ty, value })))
    }

    fn make_flags<'a>(
        ty: &Self::Type,
        names: impl IntoIterator<Item = &'a str>,
    ) -> Result<Self, WasmValueError> {
        ensure_type_kind(ty, WasmTypeKind::Flags)?;
        let flag_names = ty.flags_names().collect::<Vec<_>>();
        let mut flags = names
            .into_iter()
            .map(|name| {
                flag_names
                    .iter()
                    .position(|flag| flag == name)
                    .ok_or_else(|| WasmValueError::UnknownCase(name.into()))
            })
            .collect::<Result<Vec<_>, WasmValueError>>()?;
        // Flags values don't logically contain an ordering of the flags. Sort
        // the flags values so that equivalent flags values compare equal.
        flags.sort();
        let ty = maybe_unwrap!(&ty.0, TypeEnum::Flags).unwrap().clone();
        Ok(Self(ValueEnum::Flags(Flags { ty, flags })))
    }

    fn unwrap_float32(&self) -> f32 {
        let val = *unwrap_val!(&self.0, ValueEnum::Float32, "float32");
        canonicalize_nan32(val)
    }

    fn unwrap_float64(&self) -> f64 {
        let val = *unwrap_val!(&self.0, ValueEnum::Float64, "float64");
        canonicalize_nan64(val)
    }

    fn unwrap_string(&self) -> std::borrow::Cow<str> {
        unwrap_val!(&self.0, ValueEnum::String, "string")
            .as_ref()
            .into()
    }
    fn unwrap_list(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        let list = unwrap_val!(&self.0, ValueEnum::List, "list");
        Box::new(list.elements.iter().map(cow))
    }
    fn unwrap_record(&self) -> Box<dyn Iterator<Item = (Cow<str>, Cow<Self>)> + '_> {
        let record = unwrap_val!(&self.0, ValueEnum::Record, "record");
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
        let tuple = unwrap_val!(&self.0, ValueEnum::Tuple, "tuple");
        Box::new(tuple.elements.iter().map(cow))
    }
    fn unwrap_variant(&self) -> (Cow<str>, Option<Cow<Self>>) {
        let variant = unwrap_val!(&self.0, ValueEnum::Variant, "variant");
        let (ref name, _) = variant.ty.cases[variant.case];
        (cow(name.as_ref()), variant.payload.as_deref().map(cow))
    }
    fn unwrap_enum(&self) -> Cow<str> {
        let enum_ = unwrap_val!(&self.0, ValueEnum::Enum, "enum");
        cow(enum_.ty.cases[enum_.case].as_ref())
    }
    fn unwrap_option(&self) -> Option<Cow<Self>> {
        unwrap_val!(&self.0, ValueEnum::Option, "option")
            .value
            .as_ref()
            .map(|v| cow(v.as_ref()))
    }
    fn unwrap_result(&self) -> Result<Option<Cow<Self>>, Option<Cow<Self>>> {
        match &unwrap_val!(&self.0, ValueEnum::Result, "result").value {
            Ok(val) => Ok(val.as_deref().map(cow)),
            Err(val) => Err(val.as_deref().map(cow)),
        }
    }
    fn unwrap_flags(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        let flags = unwrap_val!(&self.0, ValueEnum::Flags, "flags");
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

fn check_type(expected: &Type, val: Value) -> Result<Value, WasmValueError> {
    if &val.ty() == expected {
        Ok(val)
    } else {
        Err(WasmValueError::wrong_value_type(expected, &val))
    }
}

fn check_payload_type(
    name: &str,
    expected: &Option<Type>,
    val: Option<Value>,
) -> Result<Option<Box<Value>>, WasmValueError> {
    match (expected, val) {
        (Some(payload_type), Some(val)) => Ok(Some(Box::new(check_type(payload_type, val)?))),
        (None, None) => Ok(None),
        (Some(_), None) => Err(WasmValueError::MissingPayload(name.into())),
        (None, Some(_)) => Err(WasmValueError::UnexpectedPayload(name.into())),
    }
}
