# WAVE: Web Assembly Value Encoding

|Type|Example Values
|---|---
|Bools|`true`, `false`
|Integers|`123`, `-9`
|Floats|`3.14`, `6.022e+23`, `nan`, `-inf`
|Chars|`'x'`, `'☃︎'`, `'\''`, `'\x00'`
|Strings|`"abc\t123"`
|Tuples|`("abc", 123)`
|Lists|`[1, 2, 3]`
|Records|`{field-a: 1, field-b: "two"}`
|Variants|`days(30)`, `forever`
|Enums|`south`, `west`
|Options|`"bare some"`, `some("explicit some")`, `none`
|Results|`"bare ok"`, `ok("explicit ok")`, `err("oops")`
|Flags|`{read, write}`, `{}`

## Usage

```rust
use wasmtime::component::{Type, Val};

let val: Val = wasm_wave::from_str(&Type::String, "\"👋 Hello, world! 👋\"").unwrap();
println!("{}", wasm_wave::to_string(&val).unwrap());
```

→ `"👋 Hello, world! 👋"`

## Encoding

Values are encoded as Unicode text. UTF-8 should be used wherever an interoperable binary encoding is required.

### Whitespace

Whitespace is _insignificant between tokens_ and _significant within tokens_: keywords, labels, chars, and strings.

### Labels

Kebab-case labels are used for record fields, variant cases, enum cases, and flags. Labels use ASCII alphanumeric characters and hyphens, following the [Component Model `label` syntax](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md).

### Bools

Bools are encoded as the keywords `false` or `true`.

### Integers

Integers are encoded as base-10 numbers.

> TBD: hex/bin repr? `0xab`, `0b1011`

### Floats

Floats are encoded as JSON numbers or one of the keywords `nan`, `inf`, or `-inf`.

### Chars

Chars are encoded as `'<char>'`, where `<char>` is one of:

- a single [Unicode Scalar Value](https://unicode.org/glossary/#unicode_scalar_value)
- one of these ASCII escapes:
  - `\'` → `'`
  - `\"` → `"`
  - `\\` → `\`
  - `\t` → 0x09 (HT)
  - `\n` → 0x0A (LF)
  - `\r` → 0x0D (CR)
  - `\x??` → 0x?? (where `??` is hex <= 0x7f)

Escaping `\` and `'` is mandatory for chars.

> TBD: Unicode escape? `\u{xxxxx}`

### Strings

Strings are encoded as a double-quote-delimited sequence of `<char>`s (as for [Chars](#chars)). Escaping `\` and `"` is mandatory for strings.

### Tuples

Tuples are encoded as a parenthesized sequence of comma-separated values. Trailing commas are permitted.

`tuple<u8, string>` → `(123, "abc")`

### Lists

Lists are encoded as a square-braketed sequence of comma-separated values. Trailing commas are permitted.

`list<char>` → `['a', 'b', 'c']`

### Records

Records are encoded as curly-braced set of comma-separated record entries. Trailing commas are permitted. Each record entry consists of a field label, a colon, and a value. Record entries with the `option`-typed value `none` may be omitted.

```clike
record example {
  must-have: u8,
  optional: option<u8>,
}
```

→ `{must-have: 123}` = `{must-have: 123, optional: none,}`

### Variants

Variants are encoded as a case label. If the case has a payload, the label is followed by the parenthesized case payload value.

`variant error { eof, other(string) }` → `other("oops")`

### Enums

Enums are encoded as a case label.

`enum hand { left, right }` → `left`

### Options

Options may be encoded in their variant form
(e.g. `some(1)` or `none`). A `some` value may also be
encoded as the "bare" payload value itself, but only if
the payload is not an option, result, variant, or enum type<sup>†</sup>.

- `option<u8>` → `123` = `some(123)`
- `option<option<u8>>` → `some(123)` = `some(some(123))`

### Results

Results may be encoded in their variant form
(e.g. `ok(1)`, `err("oops")`). An `ok` value may also be
encoded as the "bare" payload value itself, but only if
it has a payload and the payload is not an option, result, variant, or enum type<sup>†</sup>.

- `result<u8>` → `123` = `ok(123)`
- `result<_, string>` → `ok`, `err("oops")`
- `result` → `ok`, `err`

### Flags

Flags are encoded as a curly-braced set of comma-separated flag labels. Trailing commas are permitted.

`flags perms { read, write, exec }` → `{read, write,}`

> TBD: Allow record form? `{read: true, write: true, exec: false}`

### Resources

> TBD (`<named-type>(<idx>)`?)

## Appendix: Function calls

Some applications may benefit from a standard way to encode function calls and/or results, described here.

Function calls can be encoded as some application-dependent function identifier (such as a kebab-case label) followed by parenthesized function arguments.

If function results need to be encoded along with the call, they can be separated from the call by `->`.

```clike
my-func("param")
    
with-result() -> ok("result")
```

### Function arguments

Arguments are encoded as a sequence of comma-separated
values.

Any number of `option` `none` values at the end of the
sequence may be omitted.

```clike
// f: func(a: option<u8>, b: option<u8>, c: option<u8>)
// all equivalent:
f(some(1))
f(some(1), none)
f(some(1), none, none)
```

> TBD: Named-parameter encoding? e.g.
> `my-func(named-param: 1)`
> Could allow omitting "middle" `none` params.

### Function results

Results are encoded in one of several ways depending on the number of result values:

- Any number of result values may be encoded as a parenthesized sequence of comma-separated result entries. Each result entry consists of a label (for named results) or zero-based index number, a colon, and the result value. Result entry ordering must match the function definition.
- Zero result values are encoded as `()` or omitted entirely.
- A single result value may be encoded as the "bare" result value itself.

```clike
-> ()

-> some("single result")
// or
-> (0: some("single result"))
    
-> (result-a: "abc", result-b: 123)
```

---

<sup>†</sup> These payload type restrictions on "bare" `option` `some`  and `result` `ok` encodings simplify parsing and prevent ambiguity where a payload value encoding "looks like" the outer value, e.g. an `enum` with a `none` case or a `variant` with an `ok` case. While it may seem that this restriction could be loosened to only exclude types that actually have such an ambiguous case name, a subtype-compatible change to the payload type could cause previously-encoded data to become ambiguous retroactively.

:ocean:
