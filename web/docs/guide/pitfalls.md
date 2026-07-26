# Pitfalls

Use these rules when similar-looking Yulang forms parse, resolve, or infer in
different ways.

## `f(x)` vs `f (x)` vs `f: x`

```yulang
f(x)    // call
f (x)   // bare application of f to the grouped expression x
f: x    // colon application
```

These three forms parse differently: `f(x)` is the C-style call, while the
space in `f (x)` turns it into ML-style bare application. A symbol after `:`
also changes the parse, so `f:foo` and `f :foo` mean different things.

Keep the parenthesis tight to the function name for a C-style call, or drop it
for bare application. Write `f:foo` for colon application to a symbol and
`f :foo` for bare application of the symbol `:foo`.

## Method dots inside bare application

At the top level, both spellings select a field:

```yulang
xs.map double      // (xs.map) double
xs .map double     // same — `.map` still binds to xs
```

That equivalence is misleading inside a bare application. In that "ML
argument" context, a space ends the current argument, so the dot binds to the
*outer* head instead of the receiver:

```yulang
f xs.map           // f (xs.map)
f xs .map          // (f xs).map
```

When passing `xs.map` as an argument, keep the dot tight so it stays with `xs`.
Outside that context, both `xs.map` and `xs .map` are fine.

## Newlines end bare application

```yulang
f x y

f x
    y    // not bare application, this is a new statement
```

A newline closes the current bare application chain, so the indented `y` above
starts a new statement. To continue an application across lines, use
brace/colon blocks or extend the call with indentation as part of a continued
expression.

## `our` vs `pub`

The two export keywords point in different directions. Inside a `with:` block,
both are visible to other modules through the companion, but `pub` additionally
surfaces the value in the module's own type pane.

Use `our` to export a binding into the enclosing companion module, as with
methods inside `with:` and operations inside `act`. Use `pub` to export a
binding out of the module, as with top-level helpers that downstream modules
`use`.

## `error E:` variants are constructors *and* operations

```yulang
my err: path_err = path_err::not_found path    // value
path_err::not_found path                       // effect operation
```

The same name resolves either way based on context. If the expected type is
the error ADT, the expression is a constructor; if the call appears in an
effectful position, it raises the operation.

Add an annotation when the surrounding code does not fix which meaning applies.

## `fail e` is not magical

The spelling `fail e` can look like special error syntax, but `fail` is just
`\e -> e.throw` exported as a prefix operator. Replacing it with `e.throw`
still works and only makes the call site slightly noisier.

Choose `fail e` for readability, not for different error behavior.

## Refs are an effect, not a memory hole

```yulang
my $count = 0
my f() = &count = $count + 1
```

`$count` and `&count` look like direct access to a mutable cell, but they
compile to a handled `var` effect. A function that uses them has the
corresponding `var` effect row in its type unless the ref binding is in its
scope.

Keep refs within the scope where they were declared; do not treat them as
external mutable variables.

## Effects are tracked, even tiny ones

```yulang
my f() =
    say "hi"       // [console] in the row
    42
```

The function `f` has a non-empty effect row even though its only effect is a
single print. Effectful operations remain visible to inference.

Install a handler such as `run_console: f()` when the caller needs the row to
disappear.

## Anyhow-style is not available

The tempting form `catch _ -> ...` does not catch arbitrary errors, and Yulang
does not dispatch them at runtime through `Display`. Errors are caught by name.

Aggregate errors with `from`, lift them with `up`, and close them with `wrap`.
When code needs an `anyhow`-style boundary, define a wider `error E: ...` with
the right `from` entries.

## Inferring residual variables

```text
twice : Add<α> => α -> α
```

The `α` in this output is not an error. It is a residual type variable left
over because the binding is polymorphic.

Annotate the binding when the residual must be fixed to a concrete type.

## `_` is a wildcard that matches anything

```yulang
case xs:
    [_, _] -> "two elements"
    _      -> "other"
```

Each `_` matches any value and binds no name. Repeating it can therefore look
like an equality check even though the patterns are independent and can match
different values.

Give each position a name and compare them with a guard when the values must
be equal:

```yulang
case (a, b):
    (x, y) if x == y -> "same"
    _ -> "different"
```

## Operator imports are syntactic

```yulang
use my_ops::(+)
```

An operator-using expression can look like an ordinary unresolved name, but
the operator is not parsed until its import is in scope. Before that import,
the expression is a parse error rather than a name error.

Import an operator by spelling its name in parentheses, and place the import
before expressions that use it.

## Diagnose inference failures at the right layer

A function that "won't infer" can have a missing `Cast`, an unconstrained
effect tail, or a method selection waiting for more concrete information.

Start with `yulang check path/to/file.yu`; a successful check is silent, while
failures print diagnostics. Use `yulang dump path/to/file.yu --poly` to inspect
compiler IR that includes inferred binding types and role constraints.

## See also

- [Syntax Style](../reference/syntax-style) — the exact whitespace rules
- [Idioms](../reference/idioms) — the idioms that avoid these pitfalls
- [Reference](../reference/) — full feature details
