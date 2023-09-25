use wit_parser::{
    Enum, Flags, Record, Resolve, Result_, Tuple, Type, TypeDefKind, TypeId, Variant,
};

use super::{ValueError, ValueType};

/// Resolves a [`ValueType`] from the given [`wit_parser::Resolve`] and [`TypeId`].
/// # Panics
/// Panics if `type_id` is not valid in `resolve`.
pub fn resolve_wit_type(resolve: &Resolve, type_id: TypeId) -> Result<ValueType, ValueError> {
    TypeResolver { resolve }.resolve_type_id(type_id)
}

struct TypeResolver<'a> {
    resolve: &'a Resolve,
}

impl<'a> TypeResolver<'a> {
    fn resolve_type_id(&self, type_id: TypeId) -> Result<ValueType, ValueError> {
        self.resolve(&self.resolve.types.get(type_id).unwrap().kind)
    }

    fn resolve_type(&self, ty: Type) -> Result<ValueType, ValueError> {
        self.resolve(&TypeDefKind::Type(ty))
    }

    fn resolve(&self, mut kind: &'a TypeDefKind) -> Result<ValueType, ValueError> {
        // Recursively resolve any type defs.
        while let &TypeDefKind::Type(Type::Id(id)) = kind {
            kind = &self.resolve.types.get(id).unwrap().kind;
        }

        match kind {
            TypeDefKind::Record(record) => self.resolve_record(record),
            TypeDefKind::Flags(flags) => self.resolve_flags(flags),
            TypeDefKind::Tuple(tuple) => self.resolve_tuple(tuple),
            TypeDefKind::Variant(variant) => self.resolve_variant(variant),
            TypeDefKind::Enum(enum_) => self.resolve_enum(enum_),
            TypeDefKind::Option(some_type) => self.resolve_option(some_type),
            TypeDefKind::Result(result) => self.resolve_result(result),
            TypeDefKind::List(element_type) => self.resolve_list(element_type),
            TypeDefKind::Type(Type::Bool) => Ok(ValueType::BOOL),
            TypeDefKind::Type(Type::U8) => Ok(ValueType::U8),
            TypeDefKind::Type(Type::U16) => Ok(ValueType::U16),
            TypeDefKind::Type(Type::U32) => Ok(ValueType::U32),
            TypeDefKind::Type(Type::U64) => Ok(ValueType::U64),
            TypeDefKind::Type(Type::S8) => Ok(ValueType::S8),
            TypeDefKind::Type(Type::S16) => Ok(ValueType::S16),
            TypeDefKind::Type(Type::S32) => Ok(ValueType::S32),
            TypeDefKind::Type(Type::S64) => Ok(ValueType::S64),
            TypeDefKind::Type(Type::Float32) => Ok(ValueType::FLOAT32),
            TypeDefKind::Type(Type::Float64) => Ok(ValueType::FLOAT64),
            TypeDefKind::Type(Type::Char) => Ok(ValueType::CHAR),
            TypeDefKind::Type(Type::String) => Ok(ValueType::STRING),
            TypeDefKind::Type(Type::Id(_)) => unreachable!(),
            other => Err(ValueError::InvalidType(format!(
                "unsupported type {}",
                other.as_str()
            ))),
        }
    }

    fn resolve_record(&self, record: &Record) -> Result<ValueType, ValueError> {
        let fields = record
            .fields
            .iter()
            .map(|f| Ok((f.name.as_str(), self.resolve_type(f.ty)?)))
            .collect::<Result<Vec<_>, ValueError>>()?;
        Ok(ValueType::record(fields).unwrap())
    }

    fn resolve_flags(&self, flags: &Flags) -> Result<ValueType, ValueError> {
        let names = flags.flags.iter().map(|f| f.name.as_str());
        Ok(ValueType::flags(names).unwrap())
    }

    fn resolve_tuple(&self, tuple: &Tuple) -> Result<ValueType, ValueError> {
        let types = tuple
            .types
            .iter()
            .map(|ty| self.resolve_type(*ty))
            .collect::<Result<Vec<_>, ValueError>>()?;
        Ok(ValueType::tuple(types).unwrap())
    }

    fn resolve_variant(&self, variant: &Variant) -> Result<ValueType, ValueError> {
        let cases = variant
            .cases
            .iter()
            .map(|case| {
                Ok((
                    case.name.as_str(),
                    case.ty.map(|ty| self.resolve_type(ty)).transpose()?,
                ))
            })
            .collect::<Result<Vec<_>, ValueError>>()?;
        Ok(ValueType::variant(cases).unwrap())
    }

    fn resolve_enum(&self, enum_: &Enum) -> Result<ValueType, ValueError> {
        let cases = enum_.cases.iter().map(|c| c.name.as_str());
        Ok(ValueType::enum_ty(cases).unwrap())
    }

    fn resolve_option(&self, some_type: &Type) -> Result<ValueType, ValueError> {
        let some = self.resolve_type(*some_type)?;
        Ok(ValueType::option(some))
    }

    fn resolve_result(&self, result: &Result_) -> Result<ValueType, ValueError> {
        let ok = result.ok.map(|ty| self.resolve_type(ty)).transpose()?;
        let err = result.err.map(|ty| self.resolve_type(ty)).transpose()?;
        Ok(ValueType::result(ok, err))
    }

    fn resolve_list(&self, element_type: &Type) -> Result<ValueType, ValueError> {
        let element_type = self.resolve_type(*element_type)?;
        Ok(ValueType::list(element_type))
    }
}

#[cfg(test)]
mod tests {
    use wit_parser::UnresolvedPackage;

    use super::*;

    #[test]
    fn smoke_test() {
        let unresolved = UnresolvedPackage::parse(
            "test.wit".as_ref(),
            r#"
            package test:types
            interface types {
                type uint8 = u8
            }
        "#,
        )
        .unwrap();
        let mut resolve = Resolve::new();
        resolve.push(unresolved).unwrap();

        let (type_id, _) = resolve.types.iter().next().unwrap();
        let ty = resolve_wit_type(&resolve, type_id).unwrap();
        assert_eq!(ty, ValueType::U8);
    }
}
