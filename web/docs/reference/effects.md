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
say "hello"
my line = console::read()
```

Calling an operation acquires its effect on the enclosing function's type. A function that calls `console::read` has `console` in its effect row.

## Handling an effect

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(),    k -> run_console(k 42)
    console::println _, k -> run_console(k ())
```

`catch expr:` introduces a handler. Each operation arm receives the operation's arguments and a continuation `k`; calling `k value` resumes the original computation with that value. A handler may also include a final value arm `v -> ...` that runs when the inner computation completes normally.

For direct code, a handler behaves like row subtraction. If `action` has a
computation type like `[console; e] 'a`, then `run_console action` consumes the
visible `console` operations and keeps only the remaining effects.

The word "visible" matters. In higher-order code, a handler must not catch an
effect that was brought in by a caller through a function, thunk, or stored
effectful field. Yulang tracks that boundary internally with directed stack
weights. Public types still print ordinary effect rows, but the solver only
subtracts an effect when that effect is visible to the handler boundary.

### Handlers are shallow

Yulang handlers are **shallow**: a handler arm catches one operation, but the
computation resumed by `k` is not automatically wrapped in the same handler.
If the resumed computation raises the same effect again, the handler does not
fire a second time — the effect propagates outward.

To handle a stream of operations, the handler arm must rewrap the
continuation:

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console (k "42")    -- ← rewrap with run_console
    console::println _, k -> run_console (k ())
    v -> v
```

Most handlers in this reference are written in this self-recursive form for
that reason. If only a single operation is expected, the recursion can be
omitted, but for an arbitrary computation that uses the effect repeatedly the
recursion is required.

### Handler hygiene

Handler hygiene is the rule that an inner handler may handle its own visible
effects, but must not steal effects supplied by an outer caller.

```yulang
my compose f g x = f(g x)
```

If `g x` performs an effect, a handler hidden inside `f` is not allowed to catch
that effect just because both use the same effect family. The effect belongs to
the computation supplied through `g`.

This is why effect annotations do more than document a row: they also describe
which effect families are exposed across a higher-order boundary.

## Effect rows

Effect rows appear in type signatures with `[...]`:

```yulang
[console; e] str
() -> [console; e] str
```

A row lists named effects, optionally followed by a row variable such as `; e`
standing for any other effects. `[_]` can be used in annotations as a
placeholder when the exact row should be inferred, but it is not itself the
canonical type syntax for an effect row. It also does not erase a handler
boundary.

Effects may also have type arguments:

```yulang
act ref_update 'a:
    our update: 'a -> never
```

Rows can therefore contain entries such as `ref_update int`. The type printer
may render inferred rows with Greek variables; source annotations normally use
names such as `e` for row tails.

Effect-row methods are selected from the receiver's effect row, not from a
nominal value companion:

```yulang
use std::undet::*

(each [1, 2, 3]).list
```

If two effects in the same row provide a method with the same name, selection is
ambiguous until the row is constrained.

## Effect annotations and visibility

An effect row annotation has two roles:

- it describes the public row that appears in the function type;
- at higher-order boundaries, it determines what an inner handler may see.

In an argument position, an annotation like `[console] 'a` exposes only
`console` to handlers inside the receiving function. A wildcard annotation
`[_] 'a` asks inference to reuse the currently visible surface row; it is not a
request to drop hygiene evidence.

In a result position, a concrete annotation is a static filter. It checks which
effects may escape, but it does not become a runtime marker and it is not
printed as an extra public effect.

Some standard-library features, including local references, use effectful
functions stored in data values. Their internal handler evidence is private.
For example, `ref.update` may internally mention `ref_update`, but the public
type should show ordinary residual rows rather than internal stack ids or
`AllExcept(...)` evidence.

## Propagation

Effects propagate automatically. A function that calls an effectful function
acquires that effect in its own type unless it provides a handler that can see
and consume that effect.

```yulang
// ask has a type like () -> [console] str
our ask() = console::read()

// run_console removes console from the row
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
```

## `error` declarations

`error` is a shorthand that bundles an `enum`, an `act` of throwing
operations, an `impl Throw`, an `impl Display`, and the `wrap` / `up`
companion helpers into a single declaration:

```yulang
error fs_err:
    not_found path
    denied path
    invalid_path path
```

Each variant is both a constructor and a throwing effect operation. The
surrounding context selects which.

See [Errors](./errors) for the full story, including `fail`, named catch,
`wrap`, `from` aggregation, and `up`.

Ordinary `enum` variants may also use `from`; see [Casts](./casts).

## See also

- [Values & Types](./types) — function types and effect row notation.
- [Type Inference Theory](./type-theory) — stack-weighted rows and handler hygiene.
