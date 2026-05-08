# Introduction

Yulang is an experimental, statically typed language with role-based
polymorphism and algebraic effects. The implementation is still moving, so this
documentation describes the current compiler and standard library rather than a
frozen language specification.

::: tip Playground
You can try everything on this page in the <a href="/" target="_self">Playground</a>.
:::

## What makes Yulang different?

Yulang has ordinary functions and user-defined operators, but several common
features are expressed through the same mechanisms as user code:

- Operators such as `+`, `return`, `last`, and `or` are exported from the
  standard prelude rather than being parser-only builtins.
- Interfaces are written as `role` declarations and implemented with `impl`.
- Effects are declared with `act`, invoked as operations, and handled with
  `catch`.

```yulang
act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
```

## Core concepts

- **Programs are statement sequences.** Top-level expressions are evaluated and
  shown by the CLI/playground. Blocks evaluate their statements and return the
  final expression.
- **Bindings use patterns.** `my f x = ...` is a binding whose left-hand side is
  a name followed by argument patterns. `my (a, b) = pair` destructures.
- **Mutable bindings are explicit.** `my $x = ...` introduces a mutable binding;
  `$x` reads it; `&x = v` writes it.
- **Roles are interfaces.** `role Add 'a:` declares methods for a type variable,
  and `impl Add int:` implements them for `int`.
- **Effects are tracked in types.** A value such as `x: [console] int` is an
  effectful computation returning `int`; `catch` handles operations and removes
  handled effects.
- **Companions hold generated names.** `struct`, `enum`, `act`, `error`, and
  `role` create companion modules for methods, variants, operations, or role
  entries.
- **Comments.** `//` is a line comment. `--` and `---` blocks are documentation comments.

## Next steps

- [Tour](./tour) — a guided walkthrough of the language features
- [Reference](/reference/) — syntax and feature details
