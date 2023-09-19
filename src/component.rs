use std::borrow::Cow;

use crate::{ty::Kind, val::unwrap_val, Type, Val};

impl Type for wasmtime::component::Type {
    fn kind(&self) -> Kind {
        match self {
            Self::Bool => Kind::Bool,
            Self::S8 => Kind::S8,
            Self::U8 => Kind::U8,
            Self::S16 => Kind::S16,
            Self::U16 => Kind::U16,
            Self::S32 => Kind::S32,
            Self::U32 => Kind::U32,
            Self::S64 => Kind::S64,
            Self::U64 => Kind::U64,
            Self::Float32 => Kind::Float32,
            Self::Float64 => Kind::Float64,
            Self::Char => Kind::Char,
            Self::String => Kind::String,
            Self::List(_) => Kind::List,
            Self::Record(_) => Kind::Record,
            Self::Tuple(_) => Kind::Tuple,
            Self::Variant(_) => Kind::Variant,
            Self::Enum(_) => Kind::Enum,
            Self::Option(_) => Kind::Option,
            Self::Result(_) => Kind::Result,
            Self::Flags(_) => Kind::Flags,

            Self::Own(_) | Self::Borrow(_) => Kind::Unsupported,
        }
    }

    fn list_element_type(&self) -> Self {
        let Self::List(list) = self else {
            panic!("list_element_type called on non-list type");
        };
        list.ty()
    }

    fn record_fields(&self) -> Box<dyn Iterator<Item = (&str, Self)> + '_> {
        let Self::Record(record) = self else {
            panic!("record_fields called on non-record type");
        };
        Box::new(record.fields().map(|f| (f.name, f.ty)))
    }

    fn tuple_element_types(&self) -> Box<dyn Iterator<Item = Self> + '_> {
        let Self::Tuple(tuple) = self else {
            panic!("tuple_element_types called on non-tuple type");
        };
        Box::new(tuple.types())
    }

    fn variant_cases(&self) -> Box<dyn Iterator<Item = (&str, Option<Self>)> + '_> {
        let Self::Variant(variant) = self else {
            panic!("variant_cases called on non-variant type");
        };
        Box::new(variant.cases().map(|case| (case.name, case.ty)))
    }

    fn enum_cases(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        let Self::Enum(enum_) = self else {
            panic!("enum_cases called on non-enum type");
        };
        Box::new(enum_.names())
    }

    fn option_some_type(&self) -> Self {
        let Self::Option(option) = self else {
            panic!("option_some_type called on non-option type");
        };
        option.ty()
    }

    fn result_types(&self) -> (Option<Self>, Option<Self>) {
        let Self::Result(result) = self else {
            panic!("result_types called on non-result type");
        };
        (result.ok(), result.err())
    }

    fn flags_names(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        let Self::Flags(flags) = self else {
            panic!("flags_names called on non-flags type");
        };
        Box::new(flags.names())
    }
}

impl Val for wasmtime::component::Val {
    type Type = wasmtime::component::Type;
    type Error = wasmtime::Error;

    fn ty(&self) -> Self::Type {
        self.ty()
    }

    fn make_bool(val: bool) -> Self {
        Self::Bool(val)
    }
    fn make_s8(val: i8) -> Self {
        Self::S8(val)
    }
    fn make_s16(val: i16) -> Self {
        Self::S16(val)
    }
    fn make_s32(val: i32) -> Self {
        Self::S32(val)
    }
    fn make_s64(val: i64) -> Self {
        Self::S64(val)
    }
    fn make_u8(val: u8) -> Self {
        Self::U8(val)
    }
    fn make_u16(val: u16) -> Self {
        Self::U16(val)
    }
    fn make_u32(val: u32) -> Self {
        Self::U32(val)
    }
    fn make_u64(val: u64) -> Self {
        Self::U64(val)
    }
    fn make_float32(val: f32) -> Self {
        Self::Float32(val)
    }
    fn make_float64(val: f64) -> Self {
        Self::Float64(val)
    }
    fn make_char(val: char) -> Self {
        Self::Char(val)
    }
    fn make_string(val: Cow<str>) -> Self {
        Self::String(val.into())
    }
    fn make_list(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, Self::Error> {
        ty.unwrap_list().new_val(vals.into_iter().collect())
    }
    fn make_record<'a>(
        ty: &Self::Type,
        fields: impl IntoIterator<Item = (&'a str, Self)>,
    ) -> Result<Self, Self::Error> {
        ty.unwrap_record().new_val(fields)
    }
    fn make_tuple(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, Self::Error> {
        ty.unwrap_tuple().new_val(vals.into_iter().collect())
    }
    fn make_variant(ty: &Self::Type, case: &str, val: Option<Self>) -> Result<Self, Self::Error> {
        ty.unwrap_variant().new_val(case, val)
    }
    fn make_enum(ty: &Self::Type, case: &str) -> Result<Self, Self::Error> {
        ty.unwrap_enum().new_val(case)
    }
    fn make_option(ty: &Self::Type, val: Option<Self>) -> Result<Self, Self::Error> {
        ty.unwrap_option().new_val(val)
    }
    fn make_result(
        ty: &Self::Type,
        val: Result<Option<Self>, Option<Self>>,
    ) -> Result<Self, Self::Error> {
        ty.unwrap_result().new_val(val)
    }
    fn make_flags<'a>(
        ty: &Self::Type,
        names: impl IntoIterator<Item = &'a str>,
    ) -> Result<Self, Self::Error> {
        ty.unwrap_flags()
            .new_val(&names.into_iter().collect::<Vec<_>>())
    }

    fn unwrap_bool(&self) -> bool {
        *unwrap_val!(self, Self::Bool, "bool")
    }
    fn unwrap_s8(&self) -> i8 {
        *unwrap_val!(self, Self::S8, "s8")
    }
    fn unwrap_s16(&self) -> i16 {
        *unwrap_val!(self, Self::S16, "s16")
    }
    fn unwrap_s32(&self) -> i32 {
        *unwrap_val!(self, Self::S32, "s32")
    }
    fn unwrap_s64(&self) -> i64 {
        *unwrap_val!(self, Self::S64, "s64")
    }
    fn unwrap_u8(&self) -> u8 {
        *unwrap_val!(self, Self::U8, "u8")
    }
    fn unwrap_u16(&self) -> u16 {
        *unwrap_val!(self, Self::U16, "u16")
    }
    fn unwrap_u32(&self) -> u32 {
        *unwrap_val!(self, Self::U32, "u32")
    }
    fn unwrap_u64(&self) -> u64 {
        *unwrap_val!(self, Self::U64, "u64")
    }
    fn unwrap_float32(&self) -> f32 {
        *unwrap_val!(self, Self::Float32, "float32")
    }
    fn unwrap_float64(&self) -> f64 {
        *unwrap_val!(self, Self::Float64, "float64")
    }
    fn unwrap_char(&self) -> char {
        *unwrap_val!(self, Self::Char, "char")
    }
    fn unwrap_string(&self) -> Cow<str> {
        unwrap_val!(self, Self::String, "string").as_ref().into()
    }
    fn unwrap_list(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        let list = unwrap_val!(self, Self::List, "list");
        Box::new(list.iter().map(cow))
    }
    fn unwrap_record(&self) -> Box<dyn Iterator<Item = (Cow<str>, Cow<Self>)> + '_> {
        let record = unwrap_val!(self, Self::Record, "record");
        Box::new(record.fields().map(|(name, val)| (name.into(), cow(val))))
    }
    fn unwrap_tuple(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        let tuple = unwrap_val!(self, Self::Tuple, "tuple");
        Box::new(tuple.values().iter().map(cow))
    }
    fn unwrap_variant(&self) -> (Cow<str>, Option<Cow<Self>>) {
        let variant = unwrap_val!(self, Self::Variant, "variant");
        (variant.discriminant().into(), variant.payload().map(cow))
    }
    fn unwrap_enum(&self) -> Cow<str> {
        unwrap_val!(self, Self::Enum, "enum").discriminant().into()
    }
    fn unwrap_option(&self) -> Option<Cow<Self>> {
        unwrap_val!(self, Self::Option, "option").value().map(cow)
    }
    fn unwrap_result(&self) -> Result<Option<Cow<Self>>, Option<Cow<Self>>> {
        match unwrap_val!(self, Self::Result, "result").value() {
            Ok(val) => Ok(val.map(cow)),
            Err(val) => Err(val.map(cow)),
        }
    }
    fn unwrap_flags(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        let flags = unwrap_val!(self, Self::Flags, "flags");
        Box::new(flags.flags().map(Into::into))
    }
}

fn cow<T: Clone>(t: &T) -> Cow<T> {
    Cow::Borrowed(t)
}

#[cfg(test)]
mod tests {
    #[test]
    fn component_vals_smoke_test() {
        use wasmtime::component::Val;
        for (val, want) in [
            (Val::Bool(false), "false"),
            (Val::Bool(true), "true"),
            (Val::S8(10), "10"),
            (Val::S16(-10), "-10"),
            (Val::S32(1_000_000), "1000000"),
            (Val::S64(0), "0"),
            (Val::U8(255), "255"),
            (Val::U16(0), "0"),
            (Val::U32(1_000_000), "1000000"),
            (Val::U64(9), "9"),
            (Val::Float32(1.5), "1.5"),
            (Val::Float32(f32::NAN), "nan"),
            (Val::Float32(f32::INFINITY), "inf"),
            (Val::Float32(f32::NEG_INFINITY), "-inf"),
            (Val::Float64(-1.5e-10), "-0.00000000015"),
            (Val::Float64(f64::NAN), "nan"),
            (Val::Float64(f64::INFINITY), "inf"),
            (Val::Float64(f64::NEG_INFINITY), "-inf"),
            (Val::Char('x'), "'x'"),
            (Val::Char('☃'), "'☃'"),
            (Val::Char('\''), r"'\''"),
            (Val::Char('\0'), r"'\u{0}'"),
            (Val::Char('\x1b'), r"'\u{1b}'"),
            (Val::Char('😂'), r"'😂'"),
            (Val::String("abc".into()), r#""abc""#),
            (Val::String(r#"\☃""#.into()), r#""\\☃\"""#),
            (Val::String("\t\r\n\0".into()), r#""\t\r\n\u{0}""#),
        ] {
            let got = crate::to_string(&val)
                .unwrap_or_else(|err| panic!("failed to serialize {val:?}: {err}"));
            assert_eq!(got, want, "for {val:?}");
        }
    }
}
