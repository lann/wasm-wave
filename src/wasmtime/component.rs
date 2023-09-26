use std::borrow::Cow;

use crate::{
    fmt::FuncDebug,
    ty::{maybe_unwrap, WasmTypeKind},
    val::unwrap_val,
    WasmFunc, WasmType, WasmValue,
};

impl WasmType for wasmtime::component::Type {
    fn kind(&self) -> WasmTypeKind {
        match self {
            Self::Bool => WasmTypeKind::Bool,
            Self::S8 => WasmTypeKind::S8,
            Self::U8 => WasmTypeKind::U8,
            Self::S16 => WasmTypeKind::S16,
            Self::U16 => WasmTypeKind::U16,
            Self::S32 => WasmTypeKind::S32,
            Self::U32 => WasmTypeKind::U32,
            Self::S64 => WasmTypeKind::S64,
            Self::U64 => WasmTypeKind::U64,
            Self::Float32 => WasmTypeKind::Float32,
            Self::Float64 => WasmTypeKind::Float64,
            Self::Char => WasmTypeKind::Char,
            Self::String => WasmTypeKind::String,
            Self::List(_) => WasmTypeKind::List,
            Self::Record(_) => WasmTypeKind::Record,
            Self::Tuple(_) => WasmTypeKind::Tuple,
            Self::Variant(_) => WasmTypeKind::Variant,
            Self::Enum(_) => WasmTypeKind::Enum,
            Self::Option(_) => WasmTypeKind::Option,
            Self::Result(_) => WasmTypeKind::Result,
            Self::Flags(_) => WasmTypeKind::Flags,

            Self::Own(_) | Self::Borrow(_) => WasmTypeKind::Unsupported,
        }
    }

    fn list_element_type(&self) -> Option<Self> {
        Some(maybe_unwrap!(self, Self::List)?.ty())
    }

    fn record_fields(&self) -> Box<dyn Iterator<Item = (Cow<str>, Self)> + '_> {
        let Self::Record(record) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(record.fields().map(|f| (f.name.into(), f.ty.clone())))
    }

    fn tuple_element_types(&self) -> Box<dyn Iterator<Item = Self> + '_> {
        let Self::Tuple(tuple) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(tuple.types())
    }

    fn variant_cases(&self) -> Box<dyn Iterator<Item = (Cow<str>, Option<Self>)> + '_> {
        let Self::Variant(variant) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(variant.cases().map(|case| (case.name.into(), case.ty)))
    }

    fn enum_cases(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        let Self::Enum(enum_) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(enum_.names().map(Into::into))
    }

    fn option_some_type(&self) -> Option<Self> {
        maybe_unwrap!(self, Self::Option).map(|o| o.ty())
    }

    fn result_types(&self) -> Option<(Option<Self>, Option<Self>)> {
        let result = maybe_unwrap!(self, Self::Result)?;
        Some((result.ok(), result.err()))
    }

    fn flags_names(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        let Self::Flags(flags) = self else {
            return Box::new(std::iter::empty());
        };
        Box::new(flags.names().map(Into::into))
    }
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

impl WasmValue for wasmtime::component::Val {
    type Type = wasmtime::component::Type;
    type Error = wasmtime::Error;

    fn ty(&self) -> Self::Type {
        self.ty()
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

/// Represents a [`wasmtime::component::Func`] type.
#[derive(Clone)]
pub struct FuncType {
    /// The func's parameters.
    pub params: Box<[wasmtime::component::Type]>,
    /// The func's results.
    pub results: Box<[wasmtime::component::Type]>,
}

impl WasmFunc for FuncType {
    type Type = wasmtime::component::Type;

    fn params(&self) -> Box<dyn Iterator<Item = Self::Type> + '_> {
        Box::new(self.params.iter().cloned())
    }

    fn results(&self) -> Box<dyn Iterator<Item = Self::Type> + '_> {
        Box::new(self.results.iter().cloned())
    }
}

impl std::fmt::Debug for FuncType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FuncDebug(self.clone()).fmt(f)
    }
}

/// Returns a [`FuncType`] for the given `func` and `store`.
/// # Panics
/// Panics if `func` didn't come from `store`.
pub fn get_func_type(
    func: &wasmtime::component::Func,
    store: &impl wasmtime::AsContext,
) -> FuncType {
    FuncType {
        params: func.params(store),
        results: func.results(store),
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

    #[test]
    fn test_round_trip_floats() {
        use std::fmt::Debug;
        use wasmtime::component::{Type, Val};

        fn round_trip<V: crate::WasmValue + PartialEq + Debug>(ty: &V::Type, val: &V) {
            let val_str = crate::to_string(val).unwrap();
            let result: V = crate::from_str::<V>(ty, &val_str).unwrap();
            assert_eq!(val, &result);
        }

        for i in 0..100 {
            for j in 0..100 {
                round_trip(&Type::Float32, &Val::Float32(i as f32 / j as f32));
                round_trip(&Type::Float64, &Val::Float64(i as f64 / j as f64));
            }
        }

        round_trip(&Type::Float32, &Val::Float32(f32::EPSILON));
        round_trip(&Type::Float64, &Val::Float64(f64::EPSILON));
    }
}
