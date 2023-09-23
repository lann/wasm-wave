//! Formatting types.

use crate::{ty::Kind, Type};

/// Implements Debug for Types.
pub struct TypeDebug<T>(pub T);

impl<T: Type> std::fmt::Debug for TypeDebug<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ty = &self.0;
        match ty.kind() {
            Kind::List => write!(f, "list<{:?}>", Self(ty.list_element_type().unwrap())),
            Kind::Record => {
                let mut dstruct = f.debug_struct("struct");
                for (name, ty) in ty.record_fields() {
                    dstruct.field(name.as_ref(), &Self(ty));
                }
                dstruct.finish()
            }
            Kind::Tuple => {
                f.write_str("tuple<")?;
                for (idx, ty) in ty.tuple_element_types().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{:?}", Self(ty))?;
                }
                f.write_str(">")
            }
            Kind::Variant => {
                f.write_str("variant {")?;
                for (idx, (name, payload)) in ty.variant_cases().enumerate() {
                    if f.alternate() {
                        f.write_str(",\n")?;
                    } else if idx != 0 {
                        f.write_str(", ")?;
                    }
                    f.write_str(name.as_ref())?;
                    if let Some(ty) = payload {
                        write!(f, "({:?})", Self(ty))?;
                    }
                }
                f.write_str("}")
            }
            Kind::Enum => {
                f.write_str("enum {")?;
                for (idx, name) in ty.enum_cases().enumerate() {
                    if f.alternate() {
                        f.write_str(",\n")?;
                    } else if idx != 0 {
                        f.write_str(", ")?;
                    }
                    f.write_str(name.as_ref())?;
                }
                f.write_str("}")
            }
            Kind::Option => {
                write!(f, "option<{:?}>", Self(ty.option_some_type().unwrap()))
            }
            Kind::Result => {
                f.write_str("result")?;
                match ty.result_types().unwrap() {
                    (None, None) => Ok(()),
                    (None, Some(err)) => write!(f, "<_, {:?}>", Self(err)),
                    (Some(ok), None) => write!(f, "<{:?}>", Self(ok)),
                    (Some(ok), Some(err)) => write!(f, "<{:?}, {:?}>", Self(ok), Self(err)),
                }
            }
            Kind::Flags => {
                f.write_str("flags {")?;
                for (idx, name) in ty.flags_names().enumerate() {
                    if f.alternate() {
                        f.write_str(",\n")?;
                    } else if idx != 0 {
                        f.write_str(", ")?;
                    }
                    f.write_str(name.as_ref())?;
                }
                f.write_str("}")
            }
            simple => simple.fmt(f),
        }
    }
}
