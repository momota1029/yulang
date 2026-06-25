# Pitfalls

Things that surprise newcomers, with the rule of thumb to remember.

## `f(x)` vs `f (x)` vs `f: x`

```yulang
f(x)    // call
f (x)   // bare application of f to the grouped expression x
f: x    // colon application
```

These three look similar but parse differently. `f(x)` is the C-style call;
the space in `f (x)` turns it into ML-style bare application. When in doubt,
keep the parenthesis tight to the function name for a call, or drop it for
bare application.

A symbol after `:` is colon application; **`f:foo` and `f :foo` mean different
things**. Reach for explicit whitespace to make intent visible.

## Method dots inside bare application

At the top level both spellings select a field:

```yulang
xs.map double      // (xs.map) double
xs .map double     // same — `.map` still binds to xs
```

The space matters only when the dotted expression sits inside a bare
application. In that "ML argument" context a space ends the current argument,
so the dot binds to the *outer* head instead of the receiver:

```yulang
f xs.map           // f (xs.map)
f xs .map          // (f xs).map
```

If you want the dot to stay with `xs`, keep it tight when you are passing
`xs.map` as an argument. Otherwise both `xs.map` and `xs .map` are fine.

## Newlines end bare application

```yulang
f x y

f x
    y    // not bare application, this is a new statement
```

A newline closes the current bare application chain. To continue an
application across lines, use brace/colon blocks or extend the call with
indentation as part of a continued expression.

## `our` vs `pub`

`our` exports the binding **into the enclosing companion module** — the
typical choice for methods inside `with:` and operations inside `act`.

`pub` exports the binding **out of the module** for downstream files. It is
what you put on top-level helpers that other modules `use`.

Inside a `with:` block, both are visible to other modules through the
companion, but `pub` additionally surfaces the value in the module's own type
pane.

## `error E:` variants are constructors *and* operations

```yulang
my err: path_err = path_err::not_found path    // value
path_err::not_found path                       // effect operation
```

The same name resolves either way based on context. If the expected type is
the error ADT, you get the constructor; if the call appears in an effectful
position, you raise the operation. Annotate when the surrounding code does
not fix the meaning.

## `fail e` is not magical

`fail` is just `\e -> e.throw` exported as a prefix operator. If you replace
`fail` with `e.throw`, everything still works — the call site just gets
slightly noisier. The advantage of `fail` is purely readability.

## Refs are an effect, not a memory hole

```yulang
my $count = 0
my f() = &count = $count + 1
```

`$count` and `&count` compile to a handled `var` effect. A function that uses
them has the corresponding `var` row in its type unless the ref binding is in
its scope. Don't expect refs to "just be" external mutable variables outside
of where they were declared.

## Effects are tracked, even tiny ones

```yulang
my f() =
    say "hi"       // [console] in the row
    42
```

The function `f` has a non-empty effect row. A caller that wants the row to
disappear needs to install a handler (`run_console: f()`). Effectful sneak-ins
are visible to inference, so a function that "just prints" still announces
itself.

## Anyhow-style is not available

Yulang's error story is **catch by name**. There is no `catch _ -> ...`
wildcard for arbitrary errors and no runtime dispatch through `Display`.
Aggregate errors with `from`, lift them with `up`, close them with `wrap` —
all explicitly. If you find yourself wanting `anyhow`, write a wider
`error E: ...` with the right `from` entries instead.

## Inferring residual variables

```text
twice : Add<α> => α -> α
```

The `α` and `β` in inference output are not errors — they are residual type
variables left over because the binding is polymorphic. Annotating a binding
fixes the residual to a concrete type when you want it concrete.

## `_` is a fresh variable in patterns, not "anything matches"

```yulang
case xs:
    [_, _] -> "two elements"
    _      -> "other"
```

Each `_` introduces an independent fresh wildcard; they do not have to share
the same value. To bind the same value twice, name it and check with a guard:

```yulang
case (a, b):
    (x, y) if x == y -> "same"
    _ -> "different"
```

## Operator imports are syntactic

```yulang
use my_ops::(+)
```

You import operators by spelling the operator name in parentheses. The
operator is not parsed until the import is in scope, so an operator-using
expression that comes before the import is a parse error rather than a name
error.

## Where to look when things go wrong

- `yulang check path/to/file.yu` prints residual constraints and roles, which
  usually tells you what got stuck.
- A function that "won't infer" often has a missing `Cast`, an unconstrained
  effect tail, or a method selection waiting for more concrete information.

## See also

- [Syntax Style](../reference/syntax-style) — the exact whitespace rules
- [Idioms](../reference/idioms) — the idioms that avoid these pitfalls
- [Reference](../reference/) — full feature details
