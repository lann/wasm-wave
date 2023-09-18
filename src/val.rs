use std::{borrow::Cow, fmt::Display};

#[allow(unused_variables)]
pub trait Val: Clone + Sized {
    type Type: crate::ty::Type;
    type Error: Display;

    fn ty(&self) -> Self::Type;

    fn make_bool(val: bool) -> Self {
        unimplemented!()
    }
    fn make_s8(val: i8) -> Self {
        unimplemented!()
    }
    fn make_s16(val: i16) -> Self {
        unimplemented!()
    }
    fn make_s32(val: i32) -> Self {
        unimplemented!()
    }
    fn make_s64(val: i64) -> Self {
        unimplemented!()
    }
    fn make_u8(val: u8) -> Self {
        unimplemented!()
    }
    fn make_u16(val: u16) -> Self {
        unimplemented!()
    }
    fn make_u32(val: u32) -> Self {
        unimplemented!()
    }
    fn make_u64(val: u64) -> Self {
        unimplemented!()
    }
    fn make_float32(val: f32) -> Self {
        unimplemented!()
    }
    fn make_float64(val: f64) -> Self {
        unimplemented!()
    }
    fn make_char(val: char) -> Self {
        unimplemented!()
    }
    fn make_string(val: Cow<str>) -> Self {
        unimplemented!()
    }
    fn make_list(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, Self::Error> {
        unimplemented!()
    }
    fn make_record<'a>(
        ty: &Self::Type,
        fields: impl IntoIterator<Item = (&'a str, Self)>,
    ) -> Result<Self, Self::Error> {
        unimplemented!()
    }
    fn make_tuple(
        ty: &Self::Type,
        vals: impl IntoIterator<Item = Self>,
    ) -> Result<Self, Self::Error> {
        unimplemented!()
    }
    fn make_variant(ty: &Self::Type, case: &str, val: Option<Self>) -> Result<Self, Self::Error> {
        unimplemented!()
    }
    fn make_enum(ty: &Self::Type, case: &str) -> Result<Self, Self::Error> {
        unimplemented!()
    }
    fn make_option(ty: &Self::Type, val: Option<Self>) -> Result<Self, Self::Error> {
        unimplemented!()
    }
    fn make_result(
        ty: &Self::Type,
        val: Result<Option<Self>, Option<Self>>,
    ) -> Result<Self, Self::Error> {
        unimplemented!()
    }
    fn make_flags<'a>(
        ty: &Self::Type,
        names: impl IntoIterator<Item = &'a str>,
    ) -> Result<Self, Self::Error> {
        unimplemented!()
    }

    fn unwrap_bool(&self) -> bool {
        unimplemented!()
    }
    fn unwrap_s8(&self) -> i8 {
        unimplemented!()
    }
    fn unwrap_s16(&self) -> i16 {
        unimplemented!()
    }
    fn unwrap_s32(&self) -> i32 {
        unimplemented!()
    }
    fn unwrap_s64(&self) -> i64 {
        unimplemented!()
    }
    fn unwrap_u8(&self) -> u8 {
        unimplemented!()
    }
    fn unwrap_u16(&self) -> u16 {
        unimplemented!()
    }
    fn unwrap_u32(&self) -> u32 {
        unimplemented!()
    }
    fn unwrap_u64(&self) -> u64 {
        unimplemented!()
    }
    fn unwrap_float32(&self) -> f32 {
        unimplemented!()
    }
    fn unwrap_float64(&self) -> f64 {
        unimplemented!()
    }
    fn unwrap_char(&self) -> char {
        unimplemented!()
    }
    fn unwrap_string(&self) -> Cow<str> {
        unimplemented!()
    }
    fn unwrap_list(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        unimplemented!()
    }
    fn unwrap_record(&self) -> Box<dyn Iterator<Item = (Cow<str>, Cow<Self>)> + '_> {
        unimplemented!()
    }
    fn unwrap_tuple(&self) -> Box<dyn Iterator<Item = Cow<Self>> + '_> {
        unimplemented!()
    }
    fn unwrap_variant(&self) -> (Cow<str>, Option<Cow<Self>>) {
        unimplemented!()
    }
    fn unwrap_enum(&self) -> Cow<str> {
        unimplemented!()
    }
    fn unwrap_option(&self) -> Option<Cow<Self>> {
        unimplemented!()
    }
    fn unwrap_result(&self) -> Result<Option<Cow<Self>>, Option<Cow<Self>>> {
        unimplemented!()
    }
    fn unwrap_flags(&self) -> Box<dyn Iterator<Item = Cow<str>> + '_> {
        unimplemented!()
    }
}

macro_rules! unwrap_val {
    ($self:ident, $case:path, $name:expr) => {
        match $self {
            $case(v) => v,
            _ => panic!("called unwrap_{name} on non-{name} value", name = $name),
        }
    };
}

pub(crate) use unwrap_val;