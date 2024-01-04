use crate::WasmValue;

use super::{Type, Value};

#[test]
fn simple_value_round_trips() {
    for val in [
        Value::make_bool(true),
        Value::make_u8(u8::MAX),
        Value::make_u16(u16::MAX),
        Value::make_u32(u32::MAX),
        Value::make_u64(u64::MAX),
        Value::make_s8(i8::MIN),
        Value::make_s16(i16::MIN),
        Value::make_s32(i32::MIN),
        Value::make_s64(i64::MIN),
        Value::make_char('☃'),
        Value::make_string("str".into()),
    ] {
        test_value_round_trip(val)
    }
}

#[test]
fn float_round_trips() {
    for (float32, float64) in [
        (0.0, 0.0),
        (f32::MIN, f64::MIN),
        (f32::MIN_POSITIVE, f64::MIN_POSITIVE),
        (f32::MAX, f64::MAX),
        (f32::EPSILON, f64::EPSILON),
        (f32::INFINITY, f64::INFINITY),
        (f32::NEG_INFINITY, f64::NEG_INFINITY),
    ] {
        test_value_round_trip(Value::make_float32(float32));
        test_value_round_trip(Value::make_float64(float64));
    }
}

#[test]
fn list_round_trips() {
    let ty = Type::list(Type::U8);
    test_value_round_trip(Value::make_list(&ty, []).unwrap());
    test_value_round_trip(Value::make_list(&ty, [Value::make_u8(1)]).unwrap());
    test_value_round_trip(Value::make_list(&ty, [Value::make_u8(1), Value::make_u8(2)]).unwrap());
}

#[test]
fn record_round_trip() {
    let option_ty = Type::option(Type::U8);
    let record_ty =
        Type::record([("field-a", Type::BOOL), ("field-b", option_ty.clone())]).unwrap();
    let record_val = Value::make_record(
        &record_ty,
        [
            ("field-a", Value::make_bool(true)),
            ("field-b", Value::make_option(&option_ty, None).unwrap()),
        ],
    )
    .unwrap();
    test_value_round_trip(record_val)
}

#[test]
fn tuple_round_trip() {
    let ty = Type::tuple([Type::BOOL, Type::U8]).unwrap();
    let val = Value::make_tuple(&ty, [Value::make_bool(true), Value::make_u8(1)]).unwrap();
    test_value_round_trip(val);
}

#[test]
fn variant_round_trips() {
    let ty = Type::variant([("off", None), ("on", Some(Type::U8))]).unwrap();
    test_value_round_trip(Value::make_variant(&ty, "off", None).unwrap());
    test_value_round_trip(Value::make_variant(&ty, "on", Some(Value::make_u8(1))).unwrap());
}

#[test]
fn enum_round_trips() {
    let ty = Type::enum_ty(["north", "east", "south", "west"]).unwrap();
    test_value_round_trip(Value::make_enum(&ty, "north").unwrap());
    test_value_round_trip(Value::make_enum(&ty, "south").unwrap());
}

#[test]
fn option_round_trips() {
    let ty = Type::option(Type::U8);
    test_value_round_trip(Value::make_option(&ty, Some(Value::make_u8(1))).unwrap());
    test_value_round_trip(Value::make_option(&ty, None).unwrap());
}

#[test]
fn result_round_trips() {
    let no_payloads = Type::result(None, None);
    let both_payloads = Type::result(Some(Type::U8), Some(Type::STRING));
    let ok_only = Type::result(Some(Type::U8), None);
    let err_only = Type::result(None, Some(Type::STRING));
    for (ty, payload) in [
        (&no_payloads, Ok(None)),
        (&no_payloads, Err(None)),
        (&both_payloads, Ok(Some(Value::make_u8(1)))),
        (&both_payloads, Err(Some(Value::make_string("oops".into())))),
        (&ok_only, Ok(Some(Value::make_u8(1)))),
        (&ok_only, Err(None)),
        (&err_only, Ok(None)),
        (&err_only, Err(Some(Value::make_string("oops".into())))),
    ] {
        let val = Value::make_result(ty, payload).unwrap();
        test_value_round_trip(val);
    }
}

#[test]
fn flags_round_trips() {
    let ty = Type::flags(["read", "write", "execute"]).unwrap();
    test_value_round_trip(Value::make_flags(&ty, []).unwrap());
    test_value_round_trip(Value::make_flags(&ty, ["write"]).unwrap());
    test_value_round_trip(Value::make_flags(&ty, ["execute", "read"]).unwrap());
}

fn test_value_round_trip(val: Value) {
    let ty = val.ty();
    let serialized = crate::to_string(&val).unwrap();
    let deserialized: Value = crate::from_str(&ty, &serialized).unwrap();
    assert_eq!(deserialized, val, "for {val:?}");
}
