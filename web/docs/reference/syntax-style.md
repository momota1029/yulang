# Syntax Style

Yulang syntax is designed for a free-paren style: function application, colon
application, indentation, and user-defined operators carry much of the structure
that parentheses would carry in C-like languages.

This page describes the idioms that make Yulang code read naturally, and the
places where whitespace changes the parse.

## Prefer Colon for a Large Final Argument

Use `:` when the final argument is a full expression or a block.

```yulang
say: "hello"

format:
    my name = "Yulang"
    "hello, {name}"

run_console:
    my answer = ask()
    say answer
```

This keeps deeply nested calls from turning into nested parentheses.

```yulang
-- Prefer this shape.
say: format: greeting name

-- Use parentheses only when the inner colon expression must be grouped.
say (format: greeting name)
```

`f x: body` means that `x` is an ordinary argument and `body` is the colon
argument. It parses like `f x (body)`, not like `(f x:) body`.

```yulang
f x: g y z
```

## Whitespace Is Syntax

Yulang has three call-like forms that look similar but parse differently.

```yulang
f(x)    -- C-style call
f (x)   -- ML-style application of the parenthesized expression x
f: x    -- colon application
```

The same rule applies to indexing.

```yulang
xs[0]   -- index
xs [0]  -- apply xs to the list [0]
```

Symbols make the whitespace rule especially visible.

```yulang
f:foo   -- colon application: f applied to foo
f :foo  -- ML application: f applied to the symbol :foo
```

When the meaning depends on this distinction, insert the space deliberately.
Do not use `f:foo` as a compact spelling for passing a symbol.

## Newlines End ML Application

Whitespace application is line-oriented. A newline stops the current ML
application chain, unless another syntax form such as an indented colon block
continues it.

```yulang
f x y

f:
    x
    y
```

Use `:` or a grouped expression when an argument expression should continue
across a line boundary. Inside parentheses, a bare newline at the same grouping
level can be read as another tuple/group item; indent continuation lines when
the expression is meant to continue.

```yulang
f:
    g x
    h y

f (g
    x)
```

## Keep Method-Style Calls Receiver-First

Field and method selection use dot syntax. Selection itself is not a call; the
selected value is then applied by the usual call syntax.

```yulang
xs.length
xs.map f
text.splice(range 1 3, "bc")
```

Prefer receiver-first dot calls for operations that conceptually belong to the
left-hand value. Prefer `module::name` for constructors, effect operations, and
names that are primarily module exports.

```yulang
fs_err::not_found path
std::undet::each xs
```

## Use the Pipe for Left-to-Right Data Flow

The pipeline operator is `|`. It passes the left-hand value as the first
argument to the right-hand call spine.

```yulang
1 | add 2    -- add 1 2

xs
    | map f
    | filter pred
```

`|` is left-associative and binds weaker than ordinary infix operators.

```yulang
a + b | f    -- (a + b) | f
```

## Use Indentation for Blocks

Indented blocks are the normal style for multi-line bodies.

```yulang
my total xs =
    my start = 0
    fold add start xs
```

Braces are useful when the block is small or needs to stay inside another
expression.

```yulang
my inc = \x -> { x + 1 }
```

The last expression of a block is the block value.

## Prefer Header Patterns for Functions

Bindings use patterns on the left-hand side. When the head is a name, following
patterns become curried function arguments.

```yulang
my add x y = x + y
my (head, tail) = pair
my area { width = 1, height = 2 } = width * height
```

Prefer this direct header style for small functions. Use an explicit lambda
when the function value itself is the subject of the expression.

```yulang
my mapper = \f xs -> xs.map f
```

Record patterns with defaults are the idiomatic way to spell small optional
named arguments.

```yulang
my box { width = 1, height = width } = width * height

box {}
box { width: 3 }
```

Defaults are evaluated left-to-right, so later defaults may refer to earlier
fields.

## Keep `case` and `catch` Arms Vertical

Inline branches are useful for tiny expressions, but pattern-heavy code reads
better with one arm per line.

```yulang
case value:
    nil -> fallback
    just x -> x

catch action:
    console::println text, k -> k ()
    value -> value
```

Use guard clauses on the arm that owns the condition.

```yulang
case n:
    x if x < 0 -> "negative"
    _ -> "non-negative"
```

## Put Extensions in `with:` Blocks

`struct`, `enum`, `act`, `error`, `role`, and `type ... with:` declarations
create or extend a companion namespace. Put methods and nearby implementation
details in the `with:` block when they conceptually belong to the declared
thing.

```yulang
type str with:
    our s.splice r insert = std::str::splice s r insert

struct point { x: int, y: int } with:
    our p.len2 = p.x * p.x + p.y * p.y
```

This keeps receiver-style APIs close to the type or effect that owns them.

`with:` is also useful as an expression-local extension point. Put helper
bindings next to the expression that uses them when they are not part of a
type's public companion API.

```yulang
loop initial with:
    our loop state =
        if done state:
            state
        else:
            loop: step state
```

## Put Constraints Near the Binding That Needs Them

Use `where` at the point where a type variable needs a role constraint.

```yulang
my double(x: 'a): 'a =
    where 'a: Add
    x + x
```

Avoid pushing constraints into unrelated helper bindings just to make a call
typecheck. The constraint should live at the boundary whose behavior depends on
the role.

## Treat Operators as Imported Syntax

Operators are not all parser builtins. A module can define and export prefix,
infix, suffix, nullfix, and lazy infix operators.

```yulang
pub infix(+) 6.0.0 6.0.0 = add
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b -> ...
pub prefix(return) 1.0.0 = return_value
```

If downstream files must parse an operator, export/import the operator syntax
before those files are parsed. This is why public operator declarations usually
belong near the top of a module or in prelude-like modules.

Word operators such as `return`, `last`, `next`, and `redo` follow the same
operator model as symbolic operators. They should not be treated as magic parser
exceptions in user code.

## Use Lazy Operators for Short-Circuiting

Short-circuiting is written as lazy operator syntax rather than as a special
case of the evaluator.

```yulang
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b ->
    if a():
        b()
    else:
        false
```

Both operands are provided as thunks, so the body decides whether to force
each side. This makes `and`/`or` ordinary library-defined syntax with lazy
evaluation behavior.

## Add Type Annotations at Boundaries

Local code normally relies on inference.

```yulang
my id(x) = x
```

Add annotations where they communicate a public contract, reduce ambiguity, or
make an intended cast boundary explicit.

```yulang
pub my id(x: 'a): 'a = x

my result: result str fs_err = fs_err::wrap:
    read_text path
```

Type variables are written as sigil identifiers such as `'a`; they do not need
a separate binder in ordinary function declarations.

## Prefer Explicit State Syntax

Mutable or local-reference behavior is visually marked.

```yulang
my $count = 0
&count = $count + 1
```

Use this explicit form when mutation is intended, and keep ordinary `my`
bindings immutable-looking.

## Comments and Docs Are Different

Use `//` and `/* ... */` for ordinary comments.

```yulang
// local note

/* longer note */
```

Use `--` and `--- ... ---` only for documentation comments. They are parsed as
documentation syntax and may be kept by tooling.

```yulang
-- Documents the next declaration.

---
Longer documentation block.
---
```

## Summary

- Prefer whitespace application and `:` over nested parentheses.
- Use parentheses when grouping is the point, not as default punctuation.
- Prefer `my f x y = ...` for ordinary function bindings.
- Use record-pattern defaults for small optional named arguments.
- Keep pattern-heavy `case` and `catch` arms vertical.
- Put methods, attached impls, and expression-local helpers in the nearest
  natural `with:` block.
- Remember that `f(x)` and `f (x)` are different.
- Remember that `f:foo` and `f :foo` are different.
- Put exported operator syntax where importers can see it before parsing.
- Use indentation for real blocks and braces for compact inline blocks.
