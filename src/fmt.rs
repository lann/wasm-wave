//! Debug formatting types.

use crate::{ty::WasmTypeKind, WasmFunc, WasmType};

/// Implements Debug for [`WasmType`]s.
pub struct TypeDebug<T>(pub T);

impl<T: WasmType> std::fmt::Debug for TypeDebug<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ty = &self.0;
        match ty.kind() {
            WasmTypeKind::List => write!(f, "list<{:?}>", Self(ty.list_element_type().unwrap())),
            WasmTypeKind::Record => {
                f.write_str("record { ")?;
                for (idx, (name, field_type)) in ty.record_fields().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{name}: {:?}", Self(field_type))?;
                }
                f.write_str(" }")
            }
            WasmTypeKind::Tuple => {
                f.write_str("tuple<")?;
                for (idx, ty) in ty.tuple_element_types().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{:?}", Self(ty))?;
                }
                f.write_str(">")
            }
            WasmTypeKind::Variant => {
                f.write_str("variant { ")?;
                for (idx, (name, payload)) in ty.variant_cases().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    f.write_str(name.as_ref())?;
                    if let Some(ty) = payload {
                        write!(f, "({:?})", Self(ty))?;
                    }
                }
                f.write_str(" }")
            }
            WasmTypeKind::Enum => {
                f.write_str("enum { ")?;
                for (idx, name) in ty.enum_cases().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    f.write_str(name.as_ref())?;
                }
                f.write_str(" }")
            }
            WasmTypeKind::Option => {
                write!(f, "option<{:?}>", Self(ty.option_some_type().unwrap()))
            }
            WasmTypeKind::Result => {
                f.write_str("result")?;
                match ty.result_types().unwrap() {
                    (None, None) => Ok(()),
                    (None, Some(err)) => write!(f, "<_, {:?}>", Self(err)),
                    (Some(ok), None) => write!(f, "<{:?}>", Self(ok)),
                    (Some(ok), Some(err)) => write!(f, "<{:?}, {:?}>", Self(ok), Self(err)),
                }
            }
            WasmTypeKind::Flags => {
                f.write_str("flags { ")?;
                for (idx, name) in ty.flags_names().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    f.write_str(name.as_ref())?;
                }
                f.write_str(" }")
            }
            simple => std::fmt::Display::fmt(&simple, f),
        }
    }
}

/// Implements Debug for [`WasmFunc`]s.
pub struct FuncDebug<T>(pub T);

impl<T: WasmFunc> std::fmt::Debug for FuncDebug<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("func(")?;
        let mut param_names = self.0.param_names();
        for (idx, ty) in self.0.params().enumerate() {
            if idx != 0 {
                f.write_str(", ")?;
            }
            if let Some(name) = param_names.next() {
                write!(f, "{name}: ")?;
            }
            TypeDebug(ty).fmt(f)?
        }
        f.write_str(")")?;

        let results = self.0.results().collect::<Vec<_>>();
        if results.is_empty() {
            return Ok(());
        }

        let mut result_names = self.0.result_names();
        if results.len() == 1 {
            let ty = TypeDebug(results.into_iter().next().unwrap());
            if let Some(name) = result_names.next() {
                write!(f, " -> ({name}: {ty:?})")
            } else {
                write!(f, " -> {ty:?}")
            }
        } else {
            f.write_str(" -> (")?;
            for (idx, ty) in results.into_iter().enumerate() {
                if idx != 0 {
                    f.write_str(", ")?;
                }
                if let Some(name) = result_names.next() {
                    write!(f, "{name}: ")?;
                }
                TypeDebug(ty).fmt(f)?;
            }
            f.write_str(")")
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::value::Type;

    #[test]
    fn test_type_debug() {
        for (ty, expected) in [
            (Type::U8, "u8"),
            (Type::list(Type::U8), "list<u8>"),
            (
                Type::record([("a", Type::U8), ("b", Type::STRING)]).unwrap(),
                "record { a: u8, b: string }",
            ),
            (
                Type::tuple([Type::U8, Type::BOOL]).unwrap(),
                "tuple<u8, bool>",
            ),
            (
                Type::variant([("off", None), ("on", Some(Type::U8))]).unwrap(),
                "variant { off, on(u8) }",
            ),
            (
                Type::enum_ty(["east", "west"]).unwrap(),
                "enum { east, west }",
            ),
            (Type::option(Type::U8), "option<u8>"),
            (Type::result(None, None), "result"),
            (Type::result(Some(Type::U8), None), "result<u8>"),
            (Type::result(None, Some(Type::STRING)), "result<_, string>"),
            (
                Type::result(Some(Type::U8), Some(Type::STRING)),
                "result<u8, string>",
            ),
            (
                Type::flags(["read", "write"]).unwrap(),
                "flags { read, write }",
            ),
        ] {
            let debug = format!("{ty:?}");
            assert_eq!(debug, expected);
        }
    }
}
