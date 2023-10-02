use std::sync::{Mutex, OnceLock};

use wasmtime::{
    component::{Component, Instance, Linker, Type, Val},
    Config, Engine, Store,
};

#[test]
fn test_round_trips_unchanged() {
    for (func, input) in [
        ("bools", "(true, false)"),
        ("sints", "(-127, -32768, -2147483648, -9223372036854775808)"),
        ("uints", "(255, 65535, 4294967295, 18446744073709551615)"),
        ("floats", "(-1.5, 3.1415)"),
        ("floats", "(inf, inf)"),
        ("floats", "(-inf, -inf)"),
        ("floats", "(nan, nan)"),
        ("options", "(none, none)"),
        ("options", "(some(1), some(none))"),
        ("options", "(some(1), some(some(-1)))"),
        ("list-chars", "[]"),
        ("list-chars", "['x', '☃']"),
        ("list-strings", r#"["xyz", "☃☃☃", "\n\r\t"]"#),
        ("list-strings", r#"["\u{b}\u{c}\u{7f}\u{80}\u{85}\u{a0}"]"#),
        ("list-strings", r#"["\u{200d}\u{2028}\u{2029}"]"#),
        ("list-strings", r#"["\u{d7ff}\u{e000}"]"#),
        ("list-strings", r#"["\u{ffff}"]"#),
        ("list-strings", r#"["\u{feff}\u{100000}\u{10ffff}"]"#),
        ("list-strings", r#"["😂☃"]"#),
        ("result-ok-only", "ok(1)"),
        ("result-ok-only", "err"),
        ("result-err-only", "ok"),
        ("result-err-only", "err(-1)"),
        ("result-no-payloads", "ok"),
        ("result-no-payloads", "err"),
        ("result-both-payloads", "ok(1)"),
        ("result-both-payloads", "err(-1)"),
        ("record", "{required: 1}"),
        ("record", "{required: 1, optional: some(2)}"),
        ("variant", "without-payload"),
        ("variant", "with-payload(1)"),
        ("enum", "first"),
        ("enum", "second"),
        ("flags", "{}"),
        ("flags", "{read}"),
        ("flags", "{read, write}"),
    ] {
        assert_round_trip(func, input, input);
    }
}

#[test]
fn test_round_trip_variations() {
    for (func, input, output) in [
        ("bools", "(true, false, )", "(true, false)"),
        ("bools", "  (  true  ,false ,)  ", "(true, false)"),
        ("floats", "(1e+10, -5.5e-5)", "(10000000000, -0.000055)"),
        ("floats", "(0.00e100, 1.0e0)", "(0, 1)"),
        ("options", "(1, some(-1))", "(some(1), some(some(-1)))"),
        ("list-strings", "[\"a\nb\rc\td\",]", r#"["a\nb\rc\td"]"#),
        ("result-ok-only", "1", "ok(1)"),
        ("record", "{required: 1 ,optional: none ,}", "{required: 1}"),
        ("flags", "{read,}", "{read}"),
    ] {
        assert_round_trip(func, input, output);
    }
}

#[test]
fn test_wasmtime_get_func_type() {
    let func = with_instance_and_store(|instance, store| {
        let func = instance
            .exports(&mut *store)
            .root()
            .func("func-type")
            .unwrap();
        wasm_wave::wasmtime::get_func_type(&func, store)
    });

    assert_eq!(
        func.to_string(),
        "func(bool, enum { first, second }) -> result<u8>"
    );
}

fn assert_round_trip(type_name: &str, input: &str, output: &str) {
    let ty = get_type(type_name);
    let deserialized: Val = wasm_wave::from_str(&ty, input)
        .unwrap_or_else(|err| panic!("failed to deserialize {input:?}: {err}"));
    let reserialized = wasm_wave::to_string(&deserialized)
        .unwrap_or_else(|err| panic!("failed to serialize {deserialized:?}: {err}"));
    assert_eq!(reserialized, output);
}

fn with_instance_and_store<T>(f: impl Fn(&Instance, &mut Store<()>) -> T) -> T {
    static INSTANCE_AND_STORE: OnceLock<(Instance, Mutex<Store<()>>)> = OnceLock::new();
    let (instance, store) = INSTANCE_AND_STORE.get_or_init(|| {
        let engine = Engine::new(Config::new().wasm_component_model(true)).expect("engine");
        let component = Component::from_file(&engine, "tests/types.wasm").expect("component");
        let linker = Linker::new(&engine);
        let mut store = Store::new(&engine, ());
        let instance = linker
            .instantiate(&mut store, &component)
            .expect("instance");
        (instance, Mutex::new(store))
    });
    let mut store = store.lock().unwrap();
    f(instance, &mut store)
}

fn get_type(name: &str) -> Type {
    with_instance_and_store(|instance, store| {
        let func = instance
            .exports(&mut *store)
            .root()
            .func(name)
            .unwrap_or_else(|| panic!("export func named {name:?}"));
        func.results(&*store)[0].clone()
    })
}
