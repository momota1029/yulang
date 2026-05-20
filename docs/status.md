# Yulang Feature Status

Yulang is experimental. Different parts of the language move at different
speeds: some are stable enough to depend on day to day, some are still
research surface. This page tracks where each feature sits across the
pipeline so it is clear what to expect before you try it.

It complements two other documents:

- [docs/language/overview.md](language/overview.md) — what each feature does.
- [docs/native-backend.md](native-backend.md) — archived native backend status.
- [docs/native-experimental-release.md](native-experimental-release.md) —
  release-gate notes for the archived opt-in native subset.

## Legend

| Symbol | Meaning |
| :---------: | :------ |
| ✅ | Works on this stage and is exercised by tests. |
| △ | Partially works. Subset is supported, edges may differ from the interpreter oracle. |
| ❌ | Not supported on this stage yet. |
| ⚠️ | Parses or compiles, but the behavior or contract is not finalized. |
| `–` | Not applicable to this stage. |

The columns trace a value through the pipeline:

- **Parse** — accepted by `yulang-parser`.
- **Infer** — accepted by the type inference engine and produces a principal
  type.
- **Interpreter** — runs on the interpreter (the semantic oracle for everything
  else).
- **Playground** — exercised through the WebAssembly playground.
- **Archived native** — the old Cranelift/MMTk backend implementation is kept
  under `archive/yulang-native` for reference. The active workspace keeps only a
  small compatibility stub crate, and native execution is no longer exposed by
  the CLI.
- **Docs** — covered by the user-facing language overview.

## Feature support matrix

### Core expressions and bindings

| Feature                              | Parse | Infer | Interpreter | Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| `int` / `float` / `bool` / `unit` / `str` literals | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| String concatenation                 |  ✅   |  ✅   |   ✅   |     ✅     |   ✅   |  ✅  |
| Tuples, records, lists               |  ✅   |  ✅   |   ✅   |     ✅     |   ✅   |  ✅  |
| Record spread / partial record       |  ✅   |  ✅   |   ✅   |     ✅     |   ✅   |  △   |
| `my` local bindings                  |  ✅   |  ✅   |   ✅   |     ✅     |   ✅   |  ✅  |
| Top-level non-function bindings      |  ✅   |  ✅   |   ✅   |     ✅     |   ✅   |  ✅  |
| Lambdas / first-class functions      |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Closures with captured state         |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |

### Types and dispatch

| Feature                              | Parse | Infer | Interpreter | Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| Simple-Sub style inference + subtyping | ✅ | ✅  |   –    |     –      |   –    |  ✅  |
| `let` polymorphism (SCC based)       |  ✅   |  ✅   |   –    |     –      |   –    |  ✅  |
| `struct` / `enum` declarations       |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Companion methods (`with:`)          |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Roles and role constraints           |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| User-defined operators (`OpDef`)     |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Pattern matching (record / tuple / list / variant) | ✅ | ✅ | ✅ | ✅ | △ | ✅ |
| Casts / coercions                    |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  △   |

### Control flow

| Feature                              | Parse | Infer | Interpreter | Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| `sub:` / `return` early exit         |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| `for` / `last` / `next` / `redo`     |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Multi-block `if` / `else`            |  ✅   |  ✅   |   ✅   |     ✅     |   ✅   |  ✅  |
| References (`my $x`, `$x`, `&x =`)   |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |

### Effects

| Feature                              | Parse | Infer | Interpreter | Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| Effect declarations and operations   |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Algebraic handlers (`catch expr:`)   |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Effect row inference (residual rows) |  ✅   |  ✅   |   –    |     –      |   –    |  ✅  |
| `std::undet` (nondeterminism)        |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| `std::junction` (effectful boolean)  |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Multi-shot resumption                |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  △   |

### Library and host

| Feature                              | Parse | Infer | Interpreter | Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| `lib/std` prelude (numeric, list, str) | ✅  |  ✅   |   ✅   |     ✅     |   △    |  △   |
| `console::*` host effects            |  ✅   |  ✅   |   ✅   |     △      |   △    |  △   |
| `std::fs` filesystem                 |  ✅   |  ✅   |   △    |     ❌     |   ❌   |  ⚠️  |
| `error E:` sugar + `Throw` / `fail`  |  ✅   |  ✅   |   ✅   |     ✅     |   ❌   |  ✅  |
| `E::wrap` / `from` aggregation / `E::up` | ✅ | △ |   △    |     △      |   ❌   |  ✅  |
| `result 'ok 'err` value form         |  ✅   |  ✅   |   ✅   |     ✅     |   ❌   |  ✅  |
| Auto-generated `Display E`           |  ✅   |  △    |   △    |     △      |   ❌   |  △   |

### Research / preview surface

| Feature                              | Parse | Infer | Interpreter | Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| `rule { … }` parser DSL              |  ✅   |  ⚠️   |   ❌   |     ❌     |   ❌   |  ⚠️  |
| `~"..."` mark / capture syntax       |  ✅   |  ⚠️   |   ❌   |     ❌     |   ❌   |  ⚠️  |
| Parser combinator surface API        |  ✅   |  ⚠️   |   △    |     △      |   ❌   |  ⚠️  |

## Known limitations

- The old native backend implementation is archived under
  `archive/yulang-native`. The active CLI does not expose native execution; the
  interpreter/control VM path is the execution surface.
- The error vocabulary (`error E:`, `Throw` role with associated `throws`
  effect, `fail`, `wrap`, `up`, named catch) is settled at the design level
  and lands across the pipeline. The `from`-based aggregation path and the
  auto-generated `Display E` impl are still finishing up — both parse, but
  end-to-end behavior across all stages is not yet uniform.
- Library code that surfaces failures (notably `std::fs::read_text`) still
  uses provisional shapes such as `opt str` while host requests learn to
  return typed filesystem errors. These should not be treated as stable.
- `rule { … }` and `~"..."` parse, but they do not yet have a defined
  meaning as ordinary expressions and are not exposed through the runtime.
- The compiled-unit cache and the `realm.toml` / `yulang.lock` package
  workflow are not part of the main lowering pipeline yet.
- Full diagnostics polish is still in progress. Parser, type, role, and
  effect errors are being moved toward language-level explanations rather
  than internal-implementation messages.

## Reporting gaps

If you hit a behavior that is not on this matrix, or one that is marked ✅
but does not work in your case, that is useful to know. The intended path
is to capture a small reproducible Yulang snippet (the playground is fine)
and either:

- Open a GitHub issue with the snippet and the inferred / runtime output.
- Drop it under `notes/diagnostics/` as a dated bad-snippet note.

The more reproducible the snippet, the easier it is to convert into a
fixture once Yulang-facing test fixtures land.
