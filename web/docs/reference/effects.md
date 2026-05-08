# Effects

Algebraic effects are the core of Yulang's approach to side effects.

## Declaring an effect

```yulang
act console:
    our read:    () -> str
    our println: str -> ()
```

`act` declares an effect interface. Each operation is listed with a type signature using `our` (visible in the companion) or `pub` (also exported).

A companion module is generated with the same name, and operations are reachable as `console::read`, `console::println`, etc.

## Calling an effect

Effect operations are called like ordinary functions:

```yulang
println "hello"
my line = console::read()
```

Calling an operation acquires its effect on the enclosing function's type. A function that calls `console::read` has `console` in its effect row.

## Handling an effect

```yulang
our run_console(action: [console] _) = catch action:
    console::read(),    k -> run_console(k 42)
    console::println _, k -> run_console(k ())
```

`catch expr:` introduces a handler. Each operation arm receives the operation's arguments and a continuation `k`; calling `k value` resumes the original computation with that value. A handler may also include a final value arm `v -> ...` that runs when the inner computation completes normally.

The handler removes the effect from the type: if `action : [console; r] α`, then `run_console action : [r] α`.

## Effect rows

Effect rows appear in type signatures with `[...]`:

```
[console; r] str -> ()
```

A row lists named effects, optionally followed by `; r` (a row variable) standing for any other effects. A function that performs no effects has an empty row `[]` or a row variable that solves to empty.

A wildcard `[_]` is also accepted in annotations and stands for "any effects" without binding a name.

## Propagation

Effects propagate automatically. A function that calls an effectful function acquires that effect in its own type — unless it provides a handler.

```yulang
// ask has type [console] str
our ask() = console::read()

// run_console removes console from the row
our run_console(action: [console] _) = catch action:
    console::read(), k -> run_console(k "42")
```

## `error` declarations

`error` is a shorthand that produces an enum, an `act` of throwing operations, and an `impl Throw` in one declaration:

```yulang
error fs_err:
    not_found str
    denied str
    invalid_path str
```

Each variant is both a constructor (`fs_err::not_found "p"` builds an `fs_err`) and an effect operation that throws (`fs_err::not_found "p"` performs the `fs_err` effect with `never` as its result type). Which one is used depends on the surrounding type context. Variants can also be marked `from`:

```yulang
error io_err:
    fs from fs_err
```

This generates a `Cast` impl from the source error type, so an `fs_err` value implicitly lifts to an `io_err` at an annotation boundary.
