use std::sync::{Mutex, OnceLock};

use wasmtime::{
    component::{Component, Instance, Linker, Type, Val},
    Config, Engine, Store,
};

#[test]
fn test_errors() {
    for (func, input) in [
        // Reject surrogates.
        ("list-strings", "[\"\\u{d800}\"]"),
        ("list-strings", "[\"\\u{dbff}\"]"),
        ("list-strings", "[\"\\u{dc00}\"]"),
        ("list-strings", "[\"\\u{dcff}\"]"),
        ("list-strings", "[\"\\u{d800}\\u{dc00}\"]"),
        // Reject invalid values.
        ("list-strings", "[\"\\u{110000}\"]"),
        ("list-strings", "[\"\\u{ffffffff}\"]"),
        ("list-strings", "[\"\\u{80000000}\"]"),
        // Reject invalid syntax.
        ("list-strings", "[\"\\u{-1}\"]"),
        ("list-strings", "[\"\\u{+1}\"]"),
    ] {
        assert_reject(func, input);
    }
}

#[test]
fn test_option_errors() {
    for (func, input) in [
        ("options", "(some, some(some(0)))"),
        ("options", "(some(), some(some(0)))"),
        ("options", "(some(0), some(some))"),
        ("options", "(some(0), some(some()))"),
        ("options", "(some(some(0)), some(some(0)))"),
        ("options", "(some(0), some(some(some(0))))"),
        ("options", "(none(), some(some(0)))"),
        ("options", "(some(0), some(none()))"),
        ("options", "(none(0), some(some(0)))"),
        ("options", "(some(0), some(none(0)))"),
        ("options", "(some(0), none(some(0)))"),
    ] {
        assert_reject(func, input);
    }
}

#[test]
fn test_result_errors() {
    for (func, input) in [
        ("result-ok-only", "ok"),
        ("result-ok-only", "ok()"),
        ("result-ok-only", "o(0)"),
        ("result-ok-only", "err(0)"),
        ("result-err-only", "err"),
        ("result-err-only", "err()"),
        ("result-err-only", "e(0)"),
        ("result-err-only", "ok(0)"),
        ("result-no-payloads", "ok()"),
        ("result-no-payloads", "o(0)"),
        ("result-no-payloads", "ok(0)"),
        ("result-no-payloads", "err()"),
        ("result-no-payloads", "e(0)"),
        ("result-no-payloads", "err(0)"),
        ("result-both-payloads", "ok"),
        ("result-both-payloads", "ok()"),
        ("result-both-payloads", "o(0)"),
        ("result-both-payloads", "err"),
        ("result-both-payloads", "err()"),
        ("result-both-payloads", "e(0)"),
    ] {
        assert_reject(func, input);
    }
}

fn assert_reject(type_name: &str, input: &str) {
    let ty = get_type(type_name);
    let result: Result<Val, wasm_wave::parser::ParserError> = wasm_wave::from_str(&ty, input);
    match result {
        Ok(got) => panic!("failed to reject {input:?} as type {type_name}; got '{got:?}'"),
        Err(err) => {
            dbg!(err);
        }
    }
}

fn get_type(name: &str) -> Type {
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
    let func = instance
        .exports(&mut *store)
        .root()
        .func(name)
        .unwrap_or_else(|| panic!("export func named {name:?}"));
    func.results(&*store)[0].clone()
}
