# Introduction

Yulang is a statically-typed, expression-based language designed around algebraic effects.

::: tip Playground
You can try everything on this page in the <a href="/" target="_self">Playground</a>.
:::

## What makes Yulang different?

Most languages treat side effects as either unrestricted (call anything anywhere) or controlled only at the type level through monads or IO wrappers. Yulang takes a third path: **algebraic effects with static tracking**.

An effect is declared as an interface, handled at the call site, and tracked in the type. The type of a function tells you exactly what effects it may perform — and the effect can be removed by providing a handler.

```yulang
act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] _) = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
```

## Core concepts

- **Values are expressions.** Everything is an expression; blocks return their last value.
- **Mutable bindings are explicit.** `my $x = ...` introduces a mutable binding; `$x` reads it; `&x = v` writes it.
- **Effects are first-class.** Functions carry an effect row in their type: `[eff] α -> β`.
- **Roles are interfaces.** `role Add 'a:` declares an interface that types implement with `impl Add int:`.
- **Structs have companions.** `with:` attaches methods to a struct after definition.
- **Comments.** `//` is a line comment. `--` and `---` blocks are documentation comments.

## Next steps

- [Tour](./tour) — a guided walkthrough of the language features
- [Reference](/reference/) — full language specification
