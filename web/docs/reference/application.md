# Application & Operators

Yulang has several ways to write a function call. They all lower to the same curried application — the difference is purely surface syntax and how tightly each form binds.

## The four call forms

| Form | Syntax | Notes |
|------|--------|-------|
| ML-style juxtaposition | `f x y` | Whitespace-separated |
| C-style call | `f(x, y)` | **No whitespace** between callee and `(` |
| Field/method selection | `x.method`, `x.method y`, `x.method(y)` | Select a value, then optionally apply it |
| Colon block call | `f: body` | Body becomes the single argument |

The call forms lower to curried application. Dot selection by itself is a
selection; when followed by arguments, the selected value is applied:

```yulang
f x y           ≡  ((f x) y)
f(x, y)         ≡  ((f x) y)
x.method y      ≡  ((x.method) y)
x.method(y, z)  ≡  (((x.method) y) z)
```

For the C-style form there's one corner case: `f()` (empty arg list) applies `f` to the unit value `()`.

## Whitespace is significant

Yulang distinguishes "tight" postfix forms from "loose" ML-style juxtaposition by looking at trivia (whitespace and comments) **before** the next token.

```yulang
f(x)     // C-style call:    callee is f, arg is x
f (x)    // ML application:  callee is f, arg is the parenthesized (x)

xs[0]    // Index suffix:    xs.index 0
xs [0]   // ML application:  callee is xs, arg is the list literal [0]

x.field  // Method/field selection
x .field // Also field selection — leading space is allowed before `.`
```

The rule:
- `(` and `[` only count as **call/index suffixes** when they immediately follow the previous token (no leading trivia).
- `.field` is always a field/method selection at the top level — leading whitespace is allowed there. **Inside an ML argument** the space rule below applies, which can change which head a `.field` attaches to.

## Worked examples

Things get interesting when ML juxtaposition meets a tight postfix:

```yulang
f g(x)    // f (g(x))    — g and (x) are glued (no space), so `(x)` is g's call
f g (x)   // (f g) x     — space before `(` releases it to be another ML arg
f(g)(x)   // (f g) x     — two C-style calls in a row (curried)
f(g, x)   // (f g) x     — same; comma-separated args = curried
(f g)(x)  // (f g) x     — explicit grouping is just an explicit grouping
```

The same pattern with `[...]`:

```yulang
f xs[0]   // f (xs[0])   — index sticks to xs
f xs [0]  // (f xs) [0]  — space releases [0] as a list literal arg, not an index
```

And with method/field selection:

```yulang
f x.g     // f (x.g)     — `.g` glues to x
f x .g    // (f x).g     — space before `.` releases it; `.g` lands on the outer head
g.h(x)    // (g.h)(x)    — method then call
g.h (x)   // (g.h) x     — method then ML application of (x)
```

A longer chain is just left-to-right at each step:

```yulang
f.method(y).other[0] z

≡ ((((f.method)(y)).other)[0]) z
```

Why does it work this way? When parsing the right side of an ML juxtaposition, the parser is in a **tight mode** that stops at the first piece of leading whitespace. So `g(x)` (no space) keeps glueing, but `g (x)` (with space) hands control back to the outer head.

## Binding tightness

In the AST these all live at the same "tightest" level — they are postfix-style and bind left-to-right:

```yulang
f.method(y).other[0] z

≡ ((((f.method)(y)).other)[0]) z
```

Order of resolution at each step:
1. Pick the next postfix in textual order: `.method`, `(...)`, `[...]`, `::name`.
2. After all postfixes on the current head are consumed, ML-style juxtaposition takes the rest as further arguments.
3. Infix operators apply outside of all of the above, with their own precedence levels.

## Precedence vs. operators

Postfix forms (`.`, `::`, `(...)`, `[...]`) and juxtaposition all bind tighter than every infix operator in the standard prelude. Examples:

```yulang
1 + f x         // 1 + (f x)
1 + x.method    // 1 + (x.method)
1 + xs[0]       // 1 + (xs[0])
not x.field     // not (x.field)
not f x         // not (f x)
```

Prelude operators in tightest-to-loosest order:

| Level | Operators | Form |
|-------|-----------|------|
| 8     | `not`, prefix/suffix `..`, `..<`, `<..` | prefix / suffix |
| 6     | `*`, `/` | infix |
| 5     | `+`, `-` | infix |
| 4     | `..`, `..<`, `<..`, `<..<` | infix (ranges) |
| 3     | `==`, `!=`, `<`, `<=`, `>`, `>=` | infix |
| 2     | `and` | infix (lazy) |
| 1     | `or` | infix (lazy) |

So:

```yulang
1 + 2 * 3                 // 1 + (2 * 3)
a == b and c == d         // (a == b) and (c == d)
1..n + 1                  // 1..(n + 1)    -- range outside +
```

User-defined operators set their own binding powers:

```yulang
pub prefix(not) 8.0.0 = bool_not
pub infix(++) 5.0.0 5.0.1 = append
pub suffix(..) 8.0.0 = range_from
```

Binding powers are vectors of small integers, written with dots. They are
compared lexicographically; missing components compare as `0`, so `5`, `5.0`,
and `5.0.0` are equivalent, while `5.0.1` is slightly tighter than `5.0.0`.

Prefix and suffix operators each take one binding power. Infix operators take
two: left binding power and right binding power. These can differ, which is how
associativity and fine-grained grouping are expressed. For example, a right
binding power just above the left one makes the next same-level operator bind
outside the current right-hand side.

## ML application stops at whitespace boundaries

Inside an ML-style argument, the right-hand side is parsed in a "tight" mode that **stops at any whitespace before the next token**. That is what makes `f x y` group as `(f x) y` rather than `f (x y)`:

```yulang
f x y     // ((f x) y)   — left-associative
f (x y)   // explicit grouping
f x.field // f (x.field) — `.field` has no whitespace, so it sticks to x
f x .field // (f x).field — whitespace before `.` releases it to the outer
```

A newline inside an ML application also ends the argument:

```yulang
f x         // f x
my y = z    // separate statement; not an arg of f
```

## Recommended: the colon style

`expr: rest_of_line_or_block` is Yulang's idiomatic way to write a single-argument call **without parentheses**. Use this whenever the argument is "the whole rest of the expression". It binds looser than every operator and the postfix forms, so the body really is "everything to the right".

```yulang
f: g x       // f (g x)
f: g: h x    // f (g (h x))     — chains right-associatively
f: x + 1     // f (x + 1)       — operators inside the body
sub: return value  // sub (return value)
```

This is the **free-paren style**: prefer `:` over wrapping the argument in parentheses whenever you can.

```yulang
// instead of
print(format(greeting(name)))

// write
print: format: greeting name

// instead of
catch (run_console (ask ()) ):
    ...

// write
catch run_console: ask():
    ...
```

It also works with indented blocks — the body is a sequence of statements whose last expression is the value:

```yulang
run_console:
    my line = ask()
    line + "!"
```

Colon syntax is also used by several dedicated control and declaration forms.
Those forms are not all ordinary `ApplyColon` calls, but they share the same
surface habit of putting the body after `:`:

```yulang
if cond: 1 else: 2
case x:
    0 -> "zero"
    _ -> "other"
catch action:
    op a, k -> k a
for x in xs:
    println x.show
sub:
    if cond: return value
    fallback
```

### Where colon binds

Colon is **the loosest** form — looser than any infix operator. So it consumes all of its left side as the function and all of its right side as the argument:

```yulang
1 + f: x        // (1 + f) x       — `:` binds looser than `+`
f x: y          // (f x) y         — `:` is right of all juxtaposition
not f: x        // (not f) x
```

Use parentheses if you want the colon to be the inner step:

```yulang
g (f: x)        // g (f x)
1 + (f: x)      // 1 + (f x)
```

Colon does not become part of an ML argument by accident. If a colon appears
after an ML application, it binds outside that application:

```yulang
my y = f sub: 1   // (f sub): 1
my z = f (sub: 1) // f (sub: 1)
```

## `if` / `case` / `catch` are expressions

These are full expressions that can appear anywhere. They use the same `:` block form for their bodies:

```yulang
my answer = if cond: 1 else: 2
my v = case x:
    0 -> "zero"
    _ -> "other"

run: catch action:
    op a, k -> k a
```

## Lambdas

Lambdas use a leading `\`:

```yulang
\x -> x + 1
\x y -> x * y
my add = \x y -> x + y
```

Lambdas extend as far to the right as possible (the body is a full expression).

## Path separator `::`

`a::b::c` is left-associative and binds the same as the other postfix forms:

```yulang
std::list::map xs f       // ML application of (std::list::map) to xs and f
fs_err::not_found "p"     // (fs_err::not_found) "p"
```

`::` is purely a path step and never carries an effect or value of its own — it just resolves a sub-name in the left-hand companion module.
