use std::{
    collections::HashMap,
    fmt::Write,
    path::{Path, PathBuf},
    sync::OnceLock,
};

use snapbox::harness::{Case, Harness};
use wasm_wave::{
    fmt::DisplayValue,
    func::WasmFunc,
    parser::ParserError,
    value::{resolve_wit_func_type, FuncType, Value},
    Parser,
};
use wit_parser::{Resolve, UnresolvedPackage};

fn setup(path: PathBuf) -> Case {
    let name = format!("ui::{}", path.file_stem().unwrap().to_string_lossy());
    let expected = path.with_extension("out");
    Case {
        name,
        fixture: path,
        expected,
    }
}

fn test(path: &Path) -> Result<String, Box<dyn std::error::Error>> {
    let filename = path.file_name().unwrap().to_string_lossy();
    let input = std::fs::read_to_string(path)?;
    let mut output = String::new();
    let out = &mut output;
    for line in input.lines() {
        if line.starts_with("//") {
            writeln!(out, "{line}")?;
            continue;
        }
        match parse_func_call(line) {
            Ok((func_name, func_type, values)) => {
                assert!(
                    !filename.starts_with("reject-"),
                    "accepted input in in {filename}"
                );
                write!(out, "{func_name}(")?;
                let mut first = true;
                for (name, value) in func_type.param_names().zip(values) {
                    if first {
                        first = false;
                    } else {
                        write!(out, ", ")?;
                    }
                    write!(out, "{name}: {value}", value = DisplayValue(&value))?;
                }
                writeln!(out, ")")?;
            }
            Err(err) => {
                assert!(
                    !filename.starts_with("accept-"),
                    "rejected input in in {filename}"
                );
                writeln!(out, "{err}")?;
            }
        }
    }
    Ok(output)
}

fn parse_func_call(input: &str) -> Result<(&str, &'static FuncType, Vec<Value>), ParserError> {
    let (func_name, args) = Parser::new(input).parse_raw_func_call()?;
    let func_type = get_func_type(func_name).unwrap_or_else(|| {
        panic!("unknown test func {func_name:?}");
    });
    let param_types = func_type.params().collect::<Vec<_>>();
    let values = args.to_wasm_params::<Value>(&param_types)?;
    Ok((func_name, func_type, values))
}

fn get_func_type(func_name: &str) -> Option<&'static FuncType> {
    static FUNC_TYPES: OnceLock<HashMap<String, FuncType>> = OnceLock::new();
    FUNC_TYPES
        .get_or_init(|| {
            let path = Path::new("tests/ui/ui.wit");
            let unresolved = UnresolvedPackage::parse_path(path).unwrap();
            let mut resolve = Resolve::new();
            resolve.push(unresolved).unwrap();
            resolve
                .interfaces
                .iter()
                .flat_map(|(_, i)| &i.functions)
                .map(|(name, func)| (name.clone(), resolve_wit_func_type(&resolve, func).unwrap()))
                .collect::<HashMap<_, _>>()
        })
        .get(func_name)
}

fn main() {
    let action = match std::env::var("BLESS").unwrap_or_default().as_str() {
        "" => snapbox::Action::Verify,
        _ => snapbox::Action::Overwrite,
    };
    Harness::new("tests/ui", setup, test)
        .select(["*.wave"])
        .action(action)
        .test();
}
