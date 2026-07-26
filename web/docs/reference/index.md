# Reference

This page maps Yulang's top-level syntax, visibility, comments, and detailed
reference topics. Use it to find a language construct; the guide presents the
language in learning order.

## Program structure

A Yulang program is a sequence of top-level statements. Statements are
declarations (`my`, `our`, `pub`, `struct`, `enum`, `act`, `role`, `impl`,
`error`, `cast`, `type`, `use`, `mod`) and bare expressions. The Playground
evaluates bare expressions and shows the last root value; the CLI command
`yulang run --print-roots` prints root expression values.

## Visibility

| Keyword | Meaning |
|---------|---------|
| `my`    | Private binding, local or top-level |
| `our`   | Exports a binding into the enclosing companion module |
| `pub`   | Exports a binding from the module; also shows it in the Playground's Types pane |

## Comments

```yulang
// Line comment.

/* Block comment. */

-- Single-line doc comment (not a line comment).

---
Multi-line doc block.
May contain markdown and ```yulang fences.
---
```

`//` and `/* ... */` are ordinary comments. `--` and `---` blocks are
documentation comments — they appear in syntax trees and tooling, so they
are not interchangeable with `//`.

## By topic

**Surface syntax**

- [Syntax Style](./syntax-style) — when and how to drop parentheses
- [Application & Operators](./application) — how `f x`, `f(x)`, `f: x`, and `f.method` differ
- [Operator Declarations](./operators) — `infix`, `prefix`, `suffix`, precedence

**Values and types**

- [Values & Types](./types) — the type universe
- [Strings](./strings) — string layout, escapes, interpolation
- [Patterns](./patterns) — every pattern form
- [Structs & Roles](./structs) — `struct`, `with:`, `role`, `impl`
- [Casts](./casts) — `cast(x: A): B`, where the compiler inserts them

**Computation**

- [Functions](./functions) — declarations, currying, named arguments
- [Control Flow](./control-flow) — `for`, `sub:`, `case`, references
- [Effects](./effects) — `act`, `catch`, handler shapes
- [Errors](./errors) — `error`, `fail`, `from`, `up`, `wrap`

**Style**

- [Idioms](./idioms) — what idiomatic Yulang looks like

**Theory**

- [Type Inference Theory](./type-theory) — what the inferer is doing under the hood

**Standard library**

- [Core](./std/core), [list](./std/list), [str](./std/str)
- [opt](./std/opt), [result](./std/result)
- [io::file](./std/fs), [control::nondet](./std/nondet)
