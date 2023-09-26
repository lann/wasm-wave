use crate::{ty::WasmTypeKind, WasmValue};

use super::{Type, Value};

trait ValueTyped {
    fn value_type() -> Type;
}

macro_rules! impl_primitives {
    ($Self:ty, $(($case:ident, $ty:ty)),*) => {
        $(
            impl ValueTyped for $ty {
                fn value_type() -> Type {
                    Type::Simple(WasmTypeKind::$case)
                }
            }

            impl From<$ty> for $Self {
                fn from(value: $ty) -> Self {
                    Self::$case(value)
                }
            }
        )*
    };
}

impl_primitives!(
    Value,
    (Bool, bool),
    (S8, i8),
    (S16, i16),
    (S32, i32),
    (S64, i64),
    (U8, u8),
    (U16, u16),
    (U32, u32),
    (U64, u64),
    (Float32, f32),
    (Float64, f64),
    (Char, char)
);

impl ValueTyped for String {
    fn value_type() -> Type {
        Type::Simple(WasmTypeKind::String)
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::String(value.into())
    }
}

impl<'a> ValueTyped for &'a str {
    fn value_type() -> Type {
        String::value_type()
    }
}

impl<'a> From<&'a str> for Value {
    fn from(value: &'a str) -> Self {
        value.to_string().into()
    }
}

impl<const N: usize, T: ValueTyped> ValueTyped for [T; N] {
    fn value_type() -> Type {
        Type::list(T::value_type())
    }
}

impl<const N: usize, T: ValueTyped + Into<Value>> From<[T; N]> for Value {
    fn from(values: [T; N]) -> Self {
        let ty = Vec::<T>::value_type();
        let values = values.into_iter().map(Into::into);
        Value::make_list(&ty, values).unwrap()
    }
}

impl<T: ValueTyped> ValueTyped for Vec<T> {
    fn value_type() -> Type {
        Type::list(T::value_type())
    }
}

impl<T: ValueTyped + Into<Value>> From<Vec<T>> for Value {
    fn from(values: Vec<T>) -> Self {
        let ty = Vec::<T>::value_type();
        let values = values.into_iter().map(Into::into);
        Value::make_list(&ty, values).unwrap()
    }
}

impl<T: ValueTyped> ValueTyped for Option<T> {
    fn value_type() -> Type {
        Type::option(T::value_type())
    }
}

impl<T: ValueTyped + Into<Value>> From<Option<T>> for Value {
    fn from(value: Option<T>) -> Self {
        let ty = Option::<T>::value_type();
        Value::make_option(&ty, value.map(Into::into)).unwrap()
    }
}

impl<T: ValueTyped, U: ValueTyped> ValueTyped for Result<T, U> {
    fn value_type() -> Type {
        Type::result(Some(T::value_type()), Some(U::value_type()))
    }
}

impl<T: ValueTyped + Into<Value>, U: ValueTyped + Into<Value>> From<Result<T, U>> for Value {
    fn from(value: Result<T, U>) -> Self {
        let ty = Result::<T, U>::value_type();
        let value = match value {
            Ok(ok) => Ok(Some(ok.into())),
            Err(err) => Err(Some(err.into())),
        };
        Value::make_result(&ty, value).unwrap()
    }
}

macro_rules! impl_tuple {
    ($(($($var:ident),*)),*) => {
        $(
            impl<$($var: ValueTyped),*> ValueTyped for ($($var),*,) {
                fn value_type() -> Type {
                    Type::tuple(vec![$($var::value_type()),*]).unwrap()
                }
            }

            #[allow(non_snake_case)]
            impl<$($var: ValueTyped + Into<Value>),*> From<($($var),*,)> for Value {
                fn from(($($var),*,): ($($var),*,)) -> Value {
                    let ty = <($($var),*,)>::value_type();
                    $(
                        let $var = $var.into();
                    )*
                    Value::make_tuple(&ty, vec![$($var),*]).unwrap()
                }
            }

        )*
    };
}

impl_tuple!(
    (T1),
    (T1, T2),
    (T1, T2, T3),
    (T1, T2, T3, T4),
    (T1, T2, T3, T4, T5),
    (T1, T2, T3, T4, T5, T6),
    (T1, T2, T3, T4, T5, T6, T7),
    (T1, T2, T3, T4, T5, T6, T7, T8),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15),
    (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16)
);

#[cfg(test)]
mod tests {
    use crate::value::Value;

    #[test]
    fn conversions() {
        for (val, expect) in [
            (1u8.into(), "1"),
            ((-123i8).into(), "-123"),
            (f32::NAN.into(), "nan"),
            (f64::NEG_INFINITY.into(), "-inf"),
            ('x'.into(), "'x'"),
            ("str".into(), "\"str\""),
            (vec![1, 2, 3].into(), "[1, 2, 3]"),
            ([1, 2, 3].into(), "[1, 2, 3]"),
            (['a'; 3].into(), "['a', 'a', 'a']"),
            (Some(1).into(), "some(1)"),
            (None::<u8>.into(), "none"),
            (Ok::<u8, String>(1).into(), "ok(1)"),
            (Err::<u8, String>("oops".into()).into(), "err(\"oops\")"),
            ((1,).into(), "(1)"),
            ((1, "str", [9; 2]).into(), "(1, \"str\", [9, 9])"),
        ] {
            let val: Value = val;
            let got = crate::to_string(&val).unwrap();
            assert_eq!(got, expect);
        }
    }
}
