use std::borrow::Cow;

use crate::{func::WasmFunc, ty::WasmTypeKind, val::unwrap_val, WasmType, WasmValue};

impl WasmType for wasmtime::ValType {
    fn kind(&self) -> WasmTypeKind {
        match self {
            Self::I32 => WasmTypeKind::S32,
            Self::I64 => WasmTypeKind::S64,
            Self::F32 => WasmTypeKind::Float32,
            Self::F64 => WasmTypeKind::Float64,
            Self::V128 => WasmTypeKind::Tuple,

            Self::FuncRef | Self::ExternRef => WasmTypeKind::Unsupported,
        }
    }

    fn tuple_element_types(&self) -> Box<dyn Iterator<Item = Self> + '_> {
        if *self != Self::V128 {
            panic!("tuple_element_types called on non-tuple type");
        }
        Box::new([Self::I64, Self::I64].into_iter())
    }
}

impl WasmValue for wasmtime::Val {
    type Type = wasmtime::ValType;
    type Error = &'static str;

    fn ty(&self) -> Self::Type {
        self.ty()
    }

    fn make_s32(val: i32) -> Self {
        Self::I32(val)
    }
    fn make_s64(val: i64) -> Self {
        Self::I64(val)
    }
    fn make_float32(val: f32) -> Self {
        Self::F32(val.to_bits())
    }
    fn make_float64(val: f64) -> Self {
        Self::F64(val.to_bits())
    }
    fn make_tuple(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, Self::Error> {
        if *ty != Self::Type::V128 {
            return Err("tuples only used for v128 (v64x2)");
        }
        let [l_val, h_val]: [Self; 2] = vals
            .into_iter()
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|_| "expected 2 values")?;

        let (Some(l), Some(h)) = (l_val.i64(), h_val.i64()) else {
            return Err("expected 2 i64s (v64x2)");
        };
        Ok(Self::V128((h as u128) << 64 | (l as u128)))
    }

    fn unwrap_s32(&self) -> i32 {
        *unwrap_val!(self, Self::I32, "s32")
    }

    fn unwrap_s64(&self) -> i64 {
        *unwrap_val!(self, Self::I64, "s64")
    }

    fn unwrap_float32(&self) -> f32 {
        f32::from_bits(*unwrap_val!(self, Self::F32, "float32"))
    }

    fn unwrap_float64(&self) -> f64 {
        f64::from_bits(*unwrap_val!(self, Self::F64, "float64"))
    }

    fn unwrap_tuple(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        let v = *unwrap_val!(self, Self::V128, "tuple");
        let low = v as i64;
        let high = (v >> 64) as i64;
        Box::new(
            [Self::I64(low), Self::I64(high)]
                .into_iter()
                .map(Cow::Owned),
        )
    }
}

impl WasmFunc for wasmtime::FuncType {
    type Type = wasmtime::ValType;

    fn params(&self) -> Box<dyn Iterator<Item = Self::Type> + '_> {
        Box::new(self.params())
    }

    fn results(&self) -> Box<dyn Iterator<Item = Self::Type> + '_> {
        Box::new(self.results())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn core_vals_smoke_test() {
        use wasmtime::Val;
        for (val, want) in [
            (Val::I32(10), "10"),
            (Val::I64(-10), "-10"),
            (1.5f32.into(), "1.5"),
            (f32::NAN.into(), "nan"),
            (f32::INFINITY.into(), "inf"),
            (f32::NEG_INFINITY.into(), "-inf"),
            ((-1.5f64).into(), "-1.5"),
            (f32::NAN.into(), "nan"),
            (f32::INFINITY.into(), "inf"),
            (f32::NEG_INFINITY.into(), "-inf"),
            (
                Val::V128(0x1234567890abcdef1122334455667788),
                "(1234605616436508552, 1311768467294899695)",
            ),
        ] {
            let got = crate::to_string(&val)
                .unwrap_or_else(|err| panic!("failed to serialize {val:?}: {err}"));
            assert_eq!(got, want, "for {val:?}");
        }
    }
}
