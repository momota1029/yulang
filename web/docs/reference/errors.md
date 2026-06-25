# Errors

`error` is a shorthand declaration for typed errors that flow as effects.

## Declaration

```yulang
pub error io_err:
    not_found path
    denied path
    invalid_path path
```

This generates several pieces at once:

- A `pub enum io_err` whose variants are `not_found path`, `denied path`, and
  `invalid_path path`.
- A `pub act io_err` whose operations share the variant names and return
  `never`.
- An `impl Throw io_err` with `type throws = '[io_err]` and `our e.throw` that
  performs the matching effect operation.
- An `impl Display io_err` with a default text rendering (overridable with a
  hand-written impl).
- `io_err::wrap` in the companion module, which closes the error effect into
  a `result` value.
- `io_err::up` in the companion module, used when other error types declare
  `from io_err`.

## Constructors and operations share names

Each variant name is **both a data constructor and an effect operation**. The
surrounding context picks the right one.

```yulang
my err: io_err = io_err::not_found path    // built as a value
io_err::not_found path                       // raised as an effect
```

## Raising with `fail`

`fail` is a prelude prefix operator defined as a transparent wrapper around
`e.throw`:

```yulang
pub prefix(fail) = \e -> e.throw
```

Use it to surface a constructed error value into the effect row.

```yulang
my read_text_from_host path = read_text path
```

Inferred type: roughly `path -> [file, io_err] str`. The error is visible in the
effect row.

## Catching by name

`catch` arms handle errors by naming each operation directly.

```yulang
catch read_text path:
    io_err::not_found _, _ -> "(missing)"
    io_err::denied _, _ -> "(denied)"
    value -> value
```

Yulang's error story is built on **catching by name**. There is no
type-erased catch-all and no runtime dispatch over arbitrary `Display`
instances; Yulang intentionally does not provide an `anyhow`-style boundary.
Each error keeps its concrete type in the effect row, so the origin and the
handler of every error are visible from types alone.

## `wrap`: closing into a value

```yulang
my read_text_safe path = case io_err::wrap: read_text path:
    result::ok text -> text
    result::err err -> err.show
```

`E::wrap` catches the matching error effect produced by its thunk argument
and returns `result _ E`. When `E` has `from` entries, `wrap` also catches the
linked narrower errors and wraps them through the generated `Cast` impls.

## `from` aggregation

```yulang
pub error app_err:
    file from io_err
    parse from parse_err
```

This generates:

- variants `app_err::file io_err` and `app_err::parse parse_err`.
- `Cast io_err -> app_err` and `Cast parse_err -> app_err` impls.
- an extended `app_err::wrap` that also catches `io_err` and `parse_err`.
- `app_err::up`, a handler that turns the narrower errors into `app_err`.

```yulang
my read_and_parse path =
    app_err::up:
        my text = read_text path                // [io_err]
        parse_json text                          // [parse_err]
    // the block as a whole has effect [app_err]
```

See also [Casts](./casts) for the underlying conversion machinery and
[Effects](./effects) for the general `catch` and effect-row story.
