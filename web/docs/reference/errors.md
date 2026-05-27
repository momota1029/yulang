# Errors

`error` is a shorthand declaration for typed errors that flow as effects.

## Declaration

```yulang
pub error fs_err:
    not_found path
    denied path
    invalid_path path
```

This generates several pieces at once:

- A `pub enum fs_err` whose variants are `not_found path`, `denied path`, and
  `invalid_path path`.
- A `pub act fs_err` whose operations share the variant names and return
  `never`.
- An `impl Throw fs_err` with `type throws = '[fs_err]` and `our e.throw` that
  performs the matching effect operation.
- An `impl Display fs_err` with a default text rendering (overridable with a
  hand-written impl).
- `fs_err::wrap` in the companion module, which closes the error effect into
  a `result` value.
- `fs_err::up` in the companion module, used when other error types declare
  `from fs_err`.

## Constructors and operations share names

Each variant name is **both a data constructor and an effect operation**. The
surrounding context picks the right one.

```yulang
my err: fs_err = fs_err::not_found path    // built as a value
fs_err::not_found path                       // raised as an effect
```

## Raising with `fail`

`fail` is a prelude prefix operator defined as a transparent wrapper around
`e.throw`:

```yulang
pub prefix(fail) = \e -> e.throw
```

Use it to surface a constructed error value into the effect row.

```yulang
my read_text path = fs::read_text path
```

Inferred type: roughly `path -> [fs; fs_err] str`. The error is visible in the
effect row.

## Catching by name

`catch` arms handle errors by naming each operation directly.

```yulang
catch fs::read_text path:
    fs_err::not_found _, _ -> "(missing)"
    fs_err::denied _, _ -> "(denied)"
    value -> value
```

Yulang's error story is built on **catching by name**. There is no
type-erased catch-all and no runtime dispatch over arbitrary `Display`
instances; Yulang intentionally does not provide an `anyhow`-style boundary.
Each error keeps its concrete type in the effect row, so the origin and the
handler of every error are visible from types alone.

## `wrap`: closing into a value

```yulang
my read_text_safe path = case fs_err::wrap: fs::read_text path:
    result::ok text -> text
    result::err err -> err.show
```

`E::wrap` catches the matching error effect produced by its thunk argument
and returns `result _ E`. When `E` has `from` entries, `wrap` also catches the
linked narrower errors and wraps them through the generated `Cast` impls.

## `from` aggregation

```yulang
pub error io_err:
    fs from fs_err
    parse from parse_err
```

This generates:

- variants `io_err::fs fs_err` and `io_err::parse parse_err`.
- `Cast fs_err -> io_err` and `Cast parse_err -> io_err` impls.
- an extended `io_err::wrap` that also catches `fs_err` and `parse_err`.
- `io_err::up`, a handler that turns the narrower errors into `io_err`.

```yulang
my read_and_parse path =
    io_err::up:
        my text = fs::read_text path            // [fs_err]
        parse_json text                          // [parse_err]
    // the block as a whole has effect [io_err]
```

See also [Casts](./casts) for the underlying conversion machinery and
[Effects](./effects) for the general `catch` and effect-row story.
