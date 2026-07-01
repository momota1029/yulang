# Yulang Feature Status

Yulang is experimental. Different parts of the language move at different
speeds: some are stable enough to depend on day to day, some are still
research surface. This page tracks where each feature sits across the
pipeline so it is clear what to expect before you try it.

It complements these documents:

- [docs/language/overview.md](language/overview.md) — what each feature does.
- [docs/effect-inference-brief.md](effect-inference-brief.md) — the short
  outward-facing claim about hygienic effect inference.
- [docs/infer-solver-invariants.md](infer-solver-invariants.md) — the solver
  and public-signature contracts that must stay true when inference changes.
- [tests/yulang/](../tests/yulang/) — small public regression fixtures used by
  CLI and Rust tests.
- [tests/yulang/cases.toml](../tests/yulang/cases.toml) — the executable
  public contract manifest for focused CLI runtime, diagnostics, runtime
  errors, public signatures, and public examples.
- [docs/native-backend.md](native-backend.md) — archived native backend status.
- [docs/native-experimental-release.md](native-experimental-release.md) —
  release-gate notes for the archived opt-in native subset.

Archive split note: on 2026-06-14 the old `yulang` implementation was moved
to `archive/crates/` and removed from the Cargo workspace. The active CLI is
`yulang`; archived playground/native columns are historical reference points,
not build guarantees for the current workspace.

## Public Contract Spine

Yulang is past the point where adding another surface feature is the main path
to completion. The active work is to keep the existing language promises true
across inference, runtime, diagnostics, and release artifacts.

The public contract is the combination of these gates:

| Contract area | What must stay true | Main gates |
| --- | --- | --- |
| Public signatures | Printed public types do not leak private stack evidence such as `#...`, `AllExcept(...)`, or data-position private tails. Callback residuals and reference residuals must not disappear. Deep handler surfaces must not collapse into shallow handler surfaces. Manifest public-signature cases must carry exact expected types. | `cargo test -q -p yulang public -- --test-threads=1`; `tests/yulang/cases.toml`; fixtures under `tests/yulang/regressions/effect/`; [docs/infer-solver-invariants.md](infer-solver-invariants.md) |
| Runtime behavior | The default evidence VM must preserve the control/oracle behavior for public examples and focused runtime regressions. Fast paths need a proof or shape gate and must fall back to the generic route when the proof is absent. | `tests/yulang/cases.toml`; `cargo test -q -p yulang --test cli -- --test-threads=1`; `scripts/hardening-smoke.sh`; `debug evidence-vm-run --compare-control` on representative programs |
| Diagnostics | Parser, type, role/method, effect, and runtime errors should point at source-level causes. Compact CLI golden tests should check diagnostic codes/ranges/messages without freezing broad internal dumps. CLI, LSP, and playground should read the same structured diagnostic payload. Manifest `check` cases must assert count, code, severity, primary range, and related count. | `tests/yulang/cases.toml`; `public_diagnostics_check` CLI tests; `CheckReport` / `SourceDiagnostic`; LSP and wasm diagnostic tests |
| Release artifacts | A released `yulang` binary must run with the bundled standard library, start `yulang server`, keep cache status understandable, and pass public examples and hardening smoke. | `scripts/release-gate.sh`; `yulang contract tests/yulang/cases.toml`; `scripts/release-smoke.sh`; `scripts/release-archive-smoke.sh`; installer smoke scripts |
| Standard API surface | Stable APIs should be resource/lifetime contracts, not accidental thin wrappers around the current host implementation. Provisional std shapes are not compatibility promises. `std::data::result` is contract-covered by runtime and public-signature manifest cases, including `err` propagation; `std::text::path` display/byte conversion and the first `std::io::file` text API slice now have native CLI host contracts, while full file-resource metadata/locking/close semantics are still provisional. Filesystem and server APIs share host capability, scope-exit, and unsupported-host rules. | `tests/yulang/cases.toml`; [spec/2026-07-01-stable-standard-api.md](../spec/2026-07-01-stable-standard-api.md); [spec/2026-07-01-file-resource-api.md](../spec/2026-07-01-file-resource-api.md); [spec/2026-07-02-server-resource-api.md](../spec/2026-07-02-server-resource-api.md); host/filesystem/FFI TODO notes |

A change can be treated as contract-hardening when it improves one of those
gates without changing parser, inference, standard-library, or runtime
semantics by accident. A performance fast path is part of the contract only
when its fallback behavior and compare-control evidence are clear.

Not-yet-contract surfaces include the archived native backend, direct native
ABI FFI, remote package registry workflows, full parser DSL runtime exposure,
and the Yumark value model.

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
| `E::wrap` / `from` aggregation / `E::up` | ✅ | ✅ |   ✅    |     △      |   ❌   |  ✅  |
| `result 'ok 'err` value form         |  ✅   |  ✅   |   ✅   |     ✅     |   ❌   |  ✅  |
| Auto-generated `Display E`           |  ✅   |  ✅   |   ✅   |     △      |   ❌   |  ✅  |

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
  and lands across the pipeline. The basic `fail E::variant` + `E::wrap`
  flow, `from`-based aggregation through a wider `E::wrap`, the `E::up`
  lifting helper, and generated `Display E` impls are now part of the public
  manifest contract. Generated error display uses variant labels and payload
  `Display`; `from` variants delegate to the wrapped error's display. Custom
  per-variant wording is a future surface, not part of the current contract.
- `std::io::file::read_text`, `write_text`, `exists`, `is_file`, and `is_dir`
  run through the native CLI host path and return typed `io_err` effects for
  failed reads/writes. `open_text`, `open`, and `open_in` also cover the first
  managed text-ref get/set path. This is the first executable filesystem
  contract; range writes, metadata, directory listing, locking, and explicit
  close/scope-exit write-back semantics are still provisional.
- `std::text::path` is currently represented by the runtime string value
  model. `path.of_bytes`, `path.to_bytes`, and `Display path` use UTF-8 bytes
  and are covered by the public manifest. Platform-native non-UTF-8 path
  behavior is not yet a stable contract.
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
  inside a realm.
- Local editable realm/band identity is part of the release target. A directory
  with `realm.toml` is an explicit editable realm; otherwise the entry file's
  parent directory is an implicit editable realm for scripts and small
  examples. The entry file remains the root module while also owning a band
  path derived from its source path, so `realm/main::...` aliases the entry
  root instead of loading it twice. Sibling files become bands only through
  explicit `realm/...::...` imports, not by automatic directory scanning.
- Local installed realms are available through `yulang realm install <path>
  [--version <version>]` and `use local/<name>/<band>::...`. `[realm] name`
  supplies the local install name, and `[realm] version` may supply the realm's
  own release candidate version.
- The global package workflow is still experimental. Remote providers,
  version-family solving, `yulang.lock`, and registry/git source policies are
  not stable user workflows yet.
- Full diagnostics polish is still in progress. Parser, type, catch syntax, and
  role/method specialization failures now have structured CLI/LSP/playground
  payload coverage for the focused manifest cases. Role/method diagnostics use
  the specialization oracle as a narrow `SourceDiagnostic` bridge until role impl
  satisfaction has a dedicated check-stage owner.

## Reporting gaps

If you hit a behavior that is not on this matrix, or one that is marked ✅
but does not work in your case, that is useful to know. The intended path
is to capture a small reproducible Yulang snippet and either:

- Open a GitHub issue with the snippet and the inferred / runtime output.
- Drop it under `notes/diagnostics/` as a dated bad-snippet note.

The more reproducible the snippet, the easier it is to convert into a
fixture once Yulang-facing test fixtures land.
