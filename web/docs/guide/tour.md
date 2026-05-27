# Tour

A short walk through Yulang's main features. Every example here runs in the
<a href="/" target="_self">Playground</a> as-is. We go in the order "run
something" → "data and behavior" → "control flow" → "effects" → "errors".

## Basics

```yulang
1 + 2
```

A bare expression at the top level is evaluated and its value is shown. The
playground feels like a script: write, run.

```yulang
my double x = x + x
double 21
```

`my f x = ...` is a binding whose left-hand side is a name followed by
argument patterns — like OCaml's `let f x = ...` or Haskell's `f x = ...`.
For more arguments, just keep going: `my add x y = x + y`.

Visibility uses three keywords:

- `my` — private, visible only inside the current scope
- `our` — public in the enclosing companion module
- `pub` — exported out of the module

## Structs

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

`struct` declares a nominal record type, similar to Rust's or OCaml's. The
twist is `with:`, which lets you attach methods in the same declaration. The
receiver `p` stands for the value `.norm2` is called on. Convenient when
"this type comes with this behavior" and a full class would be overkill.

## Optional arguments

A record pattern with defaults gives you named optional arguments for free.

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
```

Defaults evaluate left-to-right, and later fields may reference earlier ones:

```yulang
my f {a = 1, b = a + 1, c = b + 1} = (a, b, c)
f {}             // (1, 2, 3)
f { a: 10 }      // (10, 11, 12)
```

Feels like Python keyword arguments with defaults, Ruby hash splats, or
TypeScript's `function f({a = 1} = {})`. The types are inferred — no
annotations needed.

## Mutable bindings and references

`my $x = ...` introduces a mutable binding. `$x` reads, `&x = v` writes:

```yulang
my $x = 10
&x = $x + 1
$x
```

The `$` and `&` sigils are inherited from Perl/Raku. Bindings default to
immutable; mutation has to ask for a sigil, so "state starts here" jumps out
when you skim code.

Fields and indices work the same way:

```yulang
my $xs = [2, 3, 4]
&xs[1] = 6
$xs
```

Under the hood these compile to a small `var` effect, which means mutable
state shows up in the type and cannot silently escape its binder. Not a
"variable visible from anywhere" — a "read/write port opened right here".

## Nondeterminism

`each xs` from `std::undet` picks one element of `xs`. `.list` runs the
search and collects every result:

```yulang
(each [1, 2, 3] + each [4, 5, 6]).list
```

This says "pick one from `[1,2,3]`, pick one from `[4,5,6]`, add them; give
me all combinations." Same idea as Prolog, Haskell's list monad, or a SQL
cross join — embedded into ordinary expressions.

Infinite ranges work too. Constrain later choices from earlier ones, and
`.once` returns the first success:

```yulang
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
```

You declare "I want a Pythagorean triple" and the program goes and finds
one.

## Junctions

`all` and `any` lift comparisons over collections.

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

Compare this to the Ruby spelling you would otherwise need —
`[1,2,3].all? { |x| [2,3,4].any? { |y| x < y } }`. In Yulang the comparison
stays right where you read it, because `if` accepts an effectful condition.

## Effects

`act` declares an effect interface. Operations are called like ordinary
functions, and `catch` handles them:

```yulang
act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
```

`ask()` has type `[console] int` — "returns `int`, may perform the `console`
effect." `run_console` handles the operation with `catch`, and the result
type loses `[console]`.

The `k` in a handler arm is the *continuation*. Calling `k value` resumes the
captured computation at the point where the operation was invoked. That one
mechanism gives you swappable test handlers, loops, early return, exceptions
— all of them are just choices of what to do with `k`.

## Loops and early exit

`for x in xs:` iterates over anything that implements `Fold` (lists, ranges,
…). `sub:` opens an early-return scope, and `return value` exits the nearest
`sub:`:

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```

`return` is not a parser-only keyword. The prelude exports `return` as an
operator built on the `sub` effect's `return` operation. `last`, `next`, and
`redo` work the same way — they call the loop's effect operations. "Early
exit", "break", and "continue" are applications of the same effect
machinery, not special syntax.

## Errors

`error` is sugar that produces an enum and a set of effect operations in one
go:

```yulang
error fs_err:
    not_found path
    denied path
    invalid_path path
```

`fs_err::not_found "path"` reads either as a data constructor or as a
throwing operation, depending on context:

```yulang
my err: fs_err = fs_err::not_found "/x"   // value
fs_err::not_found "/x"                     // raises [fs_err]
```

Aggregate into a wider error with `from`:

```yulang
error io_err:
    fs from fs_err
```

Errors stay named in the effect row, so "what can go wrong" is visible in
the type. There is intentionally no `Display`-erased `anyhow` wrapper —
close errors into a `result` value with `wrap` when a value-level view is
what you need.

## Comments

```yulang
// regular line comment

-- doc comment

---
multi-line doc comment
---
```

`--` is a doc comment, not an ordinary one. Use `//` for casual notes.

## Where to go next

- [Cookbook](./cookbook) — task-oriented recipes
- [Pitfalls](./pitfalls) — surprises and how to dodge them
- [Cheat Sheet](./cheat-sheet) — one-page syntax map
- [Reference](/reference/) — feature-by-feature detail
