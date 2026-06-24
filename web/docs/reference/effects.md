# Effects

Algebraic effects are the core of Yulang's approach to side effects.

## A Minimal Effect

```yulang
act flip:
    our coin: () -> bool
```

`act` declares an effect family. Each operation is listed with a type signature
using `our` (visible in the companion) or `pub` (also exported).

A companion module is generated with the same name, and operations are
reachable as `flip::coin`, `console::read`, and so on.

## Calling an effect

Effect operations are called like ordinary functions:

```yulang
my bit = flip::coin()
```

Calling an operation acquires its effect on the enclosing computation. A
function that calls `flip::coin` has `flip` in its effect row.

## Handling an effect

```yulang
our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

all_paths:
    my a = if flip::coin(): 1 else: 0
    my b = if flip::coin(): 10 else: 0
    my c = if flip::coin(): 100 else: 0
    a + b + c
```

`catch expr:` introduces a handler. Each operation arm receives the operation's arguments and a continuation `k`; calling `k value` resumes the original computation with that value. A handler may also include a final value arm `v -> ...` that runs when the inner computation completes normally.

Here `flip::coin()` looks like a function call, but it performs an operation
request. The handler receives the captured continuation `k` and resumes it once
with `true` and once with `false`, so the example enumerates all eight paths.

The important annotation is `action: [flip] _`. It is an **effect capture
contract**: this handler boundary is allowed to consume `flip`, while the value
type and any residual effects are still inferred. The inferred shape is:

```text
all_paths : 'a [flip; 'b] -> ['b] list 'a
```

Read this as: `all_paths` accepts a computation that may perform `flip` plus
some residual row `'b`; after it handles `flip`, only `'b` remains outside.

The word "visible" matters. In higher-order code, a handler must not catch an
effect that was brought in by a caller through a function, thunk, or stored
effectful field. Yulang tracks that boundary internally with directed stack
weights. Public types still print ordinary effect rows, but the solver only
subtracts an effect when that effect is visible to the handler boundary.

### Stacking handlers

Because `all_paths` leaves the residual row alone, it can be composed with
another handler that consumes a different effect:

```yulang
act amount:
    our coin: () -> int

our total_amount(action: [amount] _) =
    my loop(n, action: [amount] _) = catch action:
        amount::coin(), k -> loop(n, k n)
        v -> v
    [loop(1, action), loop(2, action)]

total_amount: all_paths:
    my a = if flip::coin(): amount::coin() else: 0
    my b = if flip::coin(): amount::coin() * 10 else: 0
    my c = if flip::coin(): amount::coin() * 100 else: 0
    a + b + c
```

`all_paths` handles only `flip` and leaves `amount`; `total_amount` handles
only `amount`. The result is a list for each `amount` interpretation:

```text
[[111, 11, 101, 1, 110, 10, 100, 0],
 [222, 22, 202, 2, 220, 20, 200, 0]]
```

This is the main reading rule for effect rows: a handler removes only the
effects it is contracted to see, and the rest of the row remains available to
outer code.

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

One way to see this is a user-defined early-return operator:

```yulang
pub act sub 'a:
    pub return: 'a -> never
    pub sub(x: [_] 'a): 'a = catch x:
        return a, _ -> a
        a -> a

our g h = sub::sub:
    h 0
    sub::return 1

sub::sub:
    g \i -> sub::return i
    sub::return 2
```

The result is `0`. The `sub::return i` inside the callback belongs to the
outer `sub::sub`, not to the handler hidden inside `g`. Without hygiene, the
inner handler could capture it accidentally and turn this into a local return
from `g`, which is usually not what higher-order code wants.

```yulang
my compose f g x = f(g x)
```

If `g x` performs an effect, a handler hidden inside `f` is not allowed to catch
that effect just because both use the same effect family. The effect belongs to
the computation supplied through `g`.

This is why effect annotations do more than document a row: they are local
contracts saying which effect families are exposed across a higher-order
boundary.

If you intentionally want `f` to handle the residual effects produced by
`g(x)`, write that contract explicitly:

```yulang
our compose(f, g: _ -> [_] _, x: [_] _) = f g(x)
```

The `x: [_] _` part says that the third argument is a computation. The
`g: _ -> [_] _` part says that the surface effects of `g(x)` may flow to `f`.
Without the `g` contract, Yulang protects the callback-origin effects from
accidental capture; compiler dumps may show that protection as evidence such as
`#0[Empty]`.

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

In an argument position, an annotation like `[console] 'a` is an effect capture
contract: handlers inside the receiving function may consume `console` from
that argument computation. A wildcard annotation `[_] 'a` is a surface contract:
the ordinary surface row remains visible, but it is not a request to discard
handler-hygiene evidence elsewhere.

When a callback parameter has no such contract, callback-origin effects are kept
hygienic. If those effects are passed into another callee, the inferred scheme
may carry an empty visibility budget, printed in compiler-oriented output as
`#id[Empty]`. This means "this occurrence cannot be subtracted at that
boundary"; it is evidence, not a new effect family.

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
