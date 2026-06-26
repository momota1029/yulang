# Yulang Feature Status

Yulang is experimental. Different parts of the language move at different
speeds: some are stable enough to depend on day to day, some are still
research surface. This page tracks where each feature sits across the
pipeline so it is clear what to expect before you try it.

It complements these documents:

- [docs/language/overview.md](language/overview.md) — what each feature does.
- [docs/effect-inference-brief.md](effect-inference-brief.md) — the short
  outward-facing claim about hygienic effect inference.
- [docs/native-backend.md](native-backend.md) — archived native backend status.
- [docs/native-experimental-release.md](native-experimental-release.md) —
  release-gate notes for the archived opt-in native subset.

Archive split note: on 2026-06-14 the old `yulang` implementation was moved
to `archive/crates/` and removed from the Cargo workspace. The active CLI is
`yulang`; archived playground/native columns are historical reference points,
not build guarantees for the current workspace.

## Legend

| Symbol | Meaning |
| :---------: | :------ |
| ✅ | Works on this stage and is exercised by tests. |
| △ | Partially works. Subset is supported, edges may differ from the interpreter oracle. |
| ❌ | Not supported on this stage yet. |
| ⚠️ | Parses or compiles, but the behavior or contract is not finalized. |
| `–` | Not applicable to this stage. |

The columns trace a value through the pipeline:

- **Parse** — accepted by `parser`.
- **Infer** — accepted by the type inference engine and produces a principal
  type.
- **Runtime** — runs through the current `yulang` runtime path where checked
  (`mono-runtime` oracle or `control-vm`).
- **Archived playground** — historical WebAssembly playground coverage from
  the old `yulang-wasm` path. It is outside the active workspace now.
- **Archived native** — historical Cranelift/MMTk support from the old native
  backend. The implementation was moved out of the active workspace to the
  local archive described in [docs/native-backend.md](native-backend.md), and
  native execution is no longer exposed by the CLI.
- **Docs** — covered by the user-facing language overview.

## Feature support matrix

### Core expressions and bindings

| Feature                              | Parse | Infer | Runtime | Archived Playground | Archived Native | Docs |
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

| Feature                              | Parse | Infer | Runtime | Archived Playground | Archived Native | Docs |
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

| Feature                              | Parse | Infer | Runtime | Archived Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| `sub:` / `return` early exit         |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| `for` / `last` / `next` / `redo`     |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Multi-block `if` / `else`            |  ✅   |  ✅   |   ✅   |     ✅     |   ✅   |  ✅  |
| References (`my $x`, `$x`, `&x =`)   |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |

### Effects

| Feature                              | Parse | Infer | Runtime | Archived Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| Effect declarations and operations   |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Algebraic handlers (`catch expr:`)   |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Effect row inference (residual rows) |  ✅   |  ✅   |   –    |     –      |   –    |  ✅  |
| `std::undet` (nondeterminism)        |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| `std::junction` (effectful boolean)  |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  ✅  |
| Multi-shot resumption                |  ✅   |  ✅   |   ✅   |     ✅     |   △    |  △   |

### Library and host

| Feature                              | Parse | Infer | Runtime | Archived Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| `lib/std` prelude (numeric, list, str) | ✅  |  ✅   |   ✅   |     ✅     |   △    |  △   |
| `console::*` host effects            |  ✅   |  ✅   |   ✅   |     △      |   △    |  △   |
| `std::fs` filesystem                 |  ✅   |  ✅   |   △    |     ❌     |   ❌   |  ⚠️  |
| `error E:` sugar + `Throw` / `fail`  |  ✅   |  ✅   |   ✅   |     ✅     |   ❌   |  ✅  |
| `E::wrap` / `from` aggregation / `E::up` | ✅ | △ |   △    |     △      |   ❌   |  ✅  |
| `result 'ok 'err` value form         |  ✅   |  ✅   |   ✅   |     ✅     |   ❌   |  ✅  |
| Auto-generated `Display E`           |  ✅   |  △    |   △    |     △      |   ❌   |  △   |

### Research / preview surface

| Feature                              | Parse | Infer | Runtime | Archived Playground | Archived Native | Docs |
| ------------------------------------ | :---: | :---: | :---------: | :--------: | :---------: | :--: |
| `rule { … }` parser DSL              |  ✅   |  ⚠️   |   ❌   |     ❌     |   ❌   |  ⚠️  |
| `~"..."` mark / capture syntax       |  ✅   |  ⚠️   |   ❌   |     ❌     |   ❌   |  ⚠️  |
| Parser combinator surface API        |  ✅   |  ⚠️   |   △    |     △      |   ❌   |  ⚠️  |

## Known limitations

- The old native backend and WebAssembly playground implementation are
  archived outside the active workspace. The active CLI does not expose native
  execution; the mono-runtime/control-VM path is the execution surface.
- The error vocabulary (`error E:`, `Throw` role with associated `throws`
  effect, `fail`, `wrap`, `up`, named catch) is settled at the design level
  and lands across the pipeline. The `from`-based aggregation path and the
  auto-generated `Display E` impl are still finishing up — both parse, but
  end-to-end behavior across all stages is not yet uniform.
- Library code that surfaces failures (notably `std::fs::read_text`) still
  uses provisional shapes such as `opt str` while host requests learn to
  return typed filesystem errors. These should not be treated as stable.
- `rule { … }` and `~"..."` lower to the `std::text::parse` combinator
  surface for the basic parser DSL. Plain tokens, lazy captures, single-item
  interpolation, alternation, and PEG-style greedy `*` / `+` / `?` quantifiers
  are covered. Regex-style lazy quantifiers are intentionally rejected by the
  active `rule` lowering; multi-item interpolation and runtime exposure are
  still incomplete.
- Quoted Yumark expressions (`'[...]` / `'{...}`) parse, but the active infer
  lowering does not assign them a value model yet.
- The compiled-unit cache is part of the normal CLI route, including exact
  full-source artifacts, std prefixes, and conservative source-unit prefixes.
  A realm is a versioned resolution space, and a band is an import/build island
  inside a realm. The `realm.toml` / `yulang.lock` package workflow is still
  not a stable user workflow, and realm/band identity is not yet the public
  dependency manager.
- Full diagnostics polish is still in progress. Parser, type, role, and
  effect errors are being moved toward language-level explanations rather
  than internal-implementation messages.

## Reporting gaps

If you hit a behavior that is not on this matrix, or one that is marked ✅
but does not work in your case, that is useful to know. The intended path
is to capture a small reproducible Yulang snippet and either:

- Open a GitHub issue with the snippet and the inferred / runtime output.
- Drop it under `notes/diagnostics/` as a dated bad-snippet note.

The more reproducible the snippet, the easier it is to convert into a
fixture once Yulang-facing test fixtures land.
