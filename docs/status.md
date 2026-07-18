# Yulang Feature Status

Yulang is experimental. Different parts of the language move at different
speeds: some are stable enough to depend on day to day, some are still
research surface. This page tracks where each feature sits across the
pipeline so it is clear what to expect before you try it.

It complements these documents:

- [docs/language/overview.md](language/overview.md) — what each feature does.
- [docs/language/stable-core.md](language/stable-core.md) — Contract v0, the
  current executable stable language core.
- [docs/language/contract-v0-evidence.md](language/contract-v0-evidence.md) —
  completion evidence for the current Contract v0 executable spine.
- [docs/language/file-resource-contract.md](language/file-resource-contract.md) —
  Contract v1, the next standard-resource contract slice.
- [docs/language/contract-v1-file-evidence.md](language/contract-v1-file-evidence.md) —
  evidence ledger for Contract v1 File Resource.
- [docs/language/server-resource-contract.md](language/server-resource-contract.md) —
  Contract v1 mock-server first slice for server resources.
- [docs/language/contract-v1-server-evidence.md](language/contract-v1-server-evidence.md) —
  evidence ledger for Contract v1 Server Resource.
- [docs/language/contract-v1-config-evidence.md](language/contract-v1-config-evidence.md) —
  evidence ledger for the unstable `std::text::config` preview slice.
- [docs/language/contract-v1-diagnostics-evidence.md](language/contract-v1-diagnostics-evidence.md) —
  evidence ledger for diagnostics gates beyond Contract v0.
- [docs/language/standard-api-contract.md](language/standard-api-contract.md) —
  current stable standard API contract slices beyond Contract v0.
- [docs/language/contract-v1-standard-api-evidence.md](language/contract-v1-standard-api-evidence.md) —
  evidence ledger for those standard API slices.
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

The public contract is the combination of these gates. The `stable-core`
manifest tag marks the **Yulang Contract v0** subset described in
[docs/language/stable-core.md](language/stable-core.md). Its current completion
evidence is recorded in
[docs/language/contract-v0-evidence.md](language/contract-v0-evidence.md);
new work should name the next contract slice it expands instead of reopening
Contract v0 as a generic TODO.

| Contract area | What must stay true | Main gates |
| --- | --- | --- |
| Public signatures | Printed public types do not leak private stack evidence such as `#...`, `AllExcept(...)`, or data-position private tails. Callback residuals and reference residuals must not disappear. Deep handler surfaces must not collapse into shallow handler surfaces. Manifest public-signature cases must carry exact expected types. | `cargo test -q -p yulang public -- --test-threads=1`; `tests/yulang/cases.toml`; fixtures under `tests/yulang/regressions/effect/`; [docs/infer-solver-invariants.md](infer-solver-invariants.md) |
| Runtime behavior | The default evidence VM must preserve the control/oracle behavior for public examples and focused runtime regressions. Fast paths need a proof or shape gate and must fall back to the generic route when the proof is absent. New runtime speedups should prefer static proof emission in mono/specialize over signal-by-signal dynamic cert checks when the static conditions are available. | `tests/yulang/cases.toml`; `cargo test -q -p yulang --test cli -- --test-threads=1`; `scripts/hardening-smoke.sh`; `debug evidence-vm-run --compare-control` on representative programs; `notes/design/2026-07-02-static-route-promotion-plan.md` |
| Diagnostics | Parser, type, role/method, effect, and runtime errors should point at source-level causes. Compact CLI golden tests should check diagnostic codes/ranges/messages without freezing broad internal dumps. CLI, LSP, and playground should read the same structured diagnostic payload. Manifest `check` cases must assert count, code, severity, primary range, and related count. Run routes must report parse diagnostics and exit non-zero before executing roots. | `tests/yulang/cases.toml`; [docs/language/contract-v1-diagnostics-evidence.md](language/contract-v1-diagnostics-evidence.md); `public_diagnostics_check` CLI tests; `CheckReport` / `SourceDiagnostic`; LSP and wasm diagnostic tests |
| Release artifacts | A released `yulang` binary must run with the bundled standard library, start `yulang server`, keep cache status understandable, and pass public examples and hardening smoke. | `scripts/release-gate.sh`; `yulang contract tests/yulang/cases.toml`; `scripts/release-smoke.sh`; `scripts/release-archive-smoke.sh`; installer smoke scripts |
| Standard API surface | Stable APIs should be resource/lifetime contracts, not accidental thin wrappers around the current host implementation. Provisional std shapes are not compatibility promises. Manifest cases distinguish `stable-api` from `migration-canary`: `std::data::result`, generated error helpers including `from`-registered `up` and automatic annotation-boundary upcast, `std::text::path` byte/display behavior, String API v1 pure helpers plus `ref '[e] str` mutating method sugar, and the Contract v1 `std::io::file` protocol center are contract-covered. The current IO resource spec fixes file / connect / serve under one `host act + session + managed view + raw` model, and the native CLI host now covers public `file::load` / `file::store` / `file::meta` protocol cases plus integrated `file::ambient_touch` / `ambient_get` / `ambient_set` handler-extent cases. Only provisional range helpers remain `migration-canary` / `raw-compat` in the file surface. The host-act canaries now also cover console source mocking and unsupported-host denial, so file and console share one capability-routing shape. Serve implementation must start from the structured concurrency decision: `accept` branches are children of the serving handler extent, cancel is queued through the scheduler, and the first slice only drops suspended branches. | `tests/yulang/cases.toml`; [docs/language/standard-api-contract.md](language/standard-api-contract.md); [docs/language/contract-v1-standard-api-evidence.md](language/contract-v1-standard-api-evidence.md); [spec/2026-07-01-stable-standard-api.md](../spec/2026-07-01-stable-standard-api.md); [spec/2026-07-02-io-resource-api.md](../spec/2026-07-02-io-resource-api.md); [spec/2026-07-01-file-resource-api.md](../spec/2026-07-01-file-resource-api.md); [spec/2026-07-02-server-resource-api.md](../spec/2026-07-02-server-resource-api.md); [notes/design/2026-07-03-structured-concurrency-decisions.md](../notes/design/2026-07-03-structured-concurrency-decisions.md); host/filesystem/FFI TODO notes |
| Config Parser Contract | Contract v1 config evidence is the unstable `std::text::config` preview slice: total parsing for honest key/value text with `[section]` headers, first-`=` splitting with trimming, `#` comments and blank lines skipped, last-wins duplicate keys, same-name section blocks merged for lookup, the `c.sections` raw escape hatch, and `load` through file effects. It is not an INI dialect, and spelling may still move before stabilization. | [docs/language/contract-v1-config-evidence.md](language/contract-v1-config-evidence.md); `tests/yulang/cases.toml` |
| File Resource Contract | Contract v1 proves that files behave like durable `&` variables across pure mock handlers, the native CLI host, and unsupported hosts. Managed text lenses follow snapshot transaction semantics: normal scope exit commits, abort rolls back, multi-shot branches keep independent buffers, and multiple commits are last-write-wins. The unscoped `$doc.lines.each` update-chain idiom now has native, source-mock, and unsupported-host evidence; unsupported hosts deny the eager `ambient_touch` before line access. The protocol center is now `stable-api`; `raw-compat` is limited to provisional range helper canaries and post-v1 session/raw API work. | [docs/language/file-resource-contract.md](language/file-resource-contract.md); [docs/language/contract-v1-file-evidence.md](language/contract-v1-file-evidence.md); [spec/2026-07-02-io-resource-api.md](../spec/2026-07-02-io-resource-api.md); [notes/design/2026-07-02-resource-lifetime-decisions.md](../notes/design/2026-07-02-resource-lifetime-decisions.md); [notes/todo/contract-v1-file-resource-priority.md](../notes/todo/contract-v1-file-resource-priority.md) |
| Server Resource Contract | Contract v1 server evidence is the `std::io::net` mock-server first slice: compiler-produced host manifest tiers, suspend multi-shot `accept` child branches, one-shot `respond`, typed `net_err::closed` double-response failure, and unscoped `net::serve` / `net::listen` spellings. Native socket behavior and unsupported-host failure are not covered yet; future host slices must report real failures rather than fake success. | [docs/language/server-resource-contract.md](language/server-resource-contract.md); [docs/language/contract-v1-server-evidence.md](language/contract-v1-server-evidence.md); [spec/2026-07-02-server-resource-api.md](../spec/2026-07-02-server-resource-api.md); [notes/design/2026-07-03-structured-concurrency-decisions.md](../notes/design/2026-07-03-structured-concurrency-decisions.md); `tests/yulang/cases.toml` |

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
| Parser pattern P1/P2 subset (`case` arms) | ✅ | ✅ | ✅ | ❌ | ❌ | ✅ |
| `rule { … }` parser DSL outside that subset | ✅ | ⚠️ | ❌ | ❌ | ❌ | ⚠️ |
| `~"..."` mark / capture syntax outside that subset | ✅ | ⚠️ | ❌ | ❌ | ❌ | ⚠️ |
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
- `std::io::file::read_text`, `write_text`, and `meta`
  run through the native CLI host path. Reads/writes return typed `io_err`
  effects for operation failures; `meta` follows the resource API decision and
  reports missing/denied/other through `file_meta.kind` instead of throwing.
  `exists`, `is_file`, and `is_dir` are pure wrappers over `meta.kind`, not
  separate host operations.
  `meta` currently returns `file_meta { kind, size, readonly, modified }`,
  with `modified` represented as `opt std::time::instant`;
  public `file::load`, `file::store`, and `file::meta` are directly covered by
  native CLI contract cases, including file, missing-target, and directory
  metadata cases that keep `exists`, `is_file`, and `is_dir` as metadata wrappers.
  Native `file::load` on a missing target and `file::store` on a directory now
  have `typed-failure` coverage that observes `io_err::not_found` and
  `io_err::failed` constructors directly. Native invalid host paths now
  classify `InvalidInput` / `InvalidData` as `io_err::invalid_path` through both
  protocol operations and text helpers, so the contract surface does not rely on
  an integer error-code bridge or collapse invalid paths into generic failure.
  `read_at` / `write_at`
  now return typed
  `result ... io_err` values at the host act boundary while preserving the
  existing throwing public wrappers, and the runtime manifest classifies them as
  `raw-compat` because range semantics remain provisional. The old
  `open_text` / `open` / `open_in` snapshot helper surface and its private
  raw host operations are retired from `std::io::file` and from the runtime
  host manifest; the old integer-code mapper is gone.
  `text_with` is now the state-passing protocol
  over public `load` / `store`: native normal commit, callback-abort rollback,
  nondet branch-local last-write-wins, nested cross-file sessions, and nested
  state-var capture are executable manifest cases, and source mock handlers
  cover commit, rollback, branch-local buffers, and nested cross-file sessions
  under `--host unsupported`. The compiler-produced host manifest now exposes
  `surface=contract|raw-compat`, replay `column` values, deterministic
  `symbol` names, and a manifest `hash`; Stage A of the Contract v1 Stage 2
  closeout leaves only the provisional range helpers on `raw-compat`. This
  still leaves directory listing, portable metadata
  expansion, and lock release provisional. Unsupported host coverage now goes
  through the unified `file`
  act, so ambient `text` does not fake success under `--host unsupported`;
  native `file::text` missing-path creation reports typed `io_err::not_found`,
  while direct out-of-protocol `file::ambient_get` / `file::ambient_set` still
  report structured `yulang.host-io-error` as specified by the Stage 2
  closeout decision.
  resource lifetime semantics are specified: `_with` resources close at
  continuation end, unscoped resources close at the provider handler extent,
  managed lens commits only on normal scope exit, aborted branches roll back,
  and first-slice lock release may stay tied to handler discharge.
- `std::time` now provides public `instant { epoch_nanos }` and
  `duration { nanos }` values, `Eq` / `Ord` impls, named instant/duration
  arithmetic helpers, duration unit constructors (`nanos` through `days`), and
  the `std::time::clock.now` host act. `instant.show` formats RFC 3339 UTC and
  `instant.debug` / `duration.debug` keep structural output. `clock.now` is a
  wall-clock host operation, not a monotonic timer; performance timing should
  continue to use runtime instrumentation rather than `instant`.
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
- Quoted Yumark expressions (`'[...]` / `'{...}`) now use the production
  algebra-passing value model and full static-vocabulary lowering, with HTML
  and Markdown algebras in `lib/std/text/yumark.yu`. The LS lazy per-hover path
  is live for its safe doc-comment subset, backed by a resident warm evaluator
  and static fallback. `YmCommand` / `YmInlineExpr` injection remains
  unsupported, Yumark algebra operations do not yet carry source spans, and a
  dedicated playground preview has not been built. Making lazy hover the
  default / primary policy is an intentionally deferred product decision, not
  a technical blocker.
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
- Full diagnostics polish is still in progress. Parser, type, catch syntax,
  role/method specialization failures, and focused runtime failures now have
  manifest coverage. Check-stage cases carry structured CLI/LSP/playground
  payloads; runtime-failure cases pin the user-facing code and hint text,
  including representative unsupported-host capability failures.
  Since 2026-07-03, role/method diagnostics have used the dedicated,
  emission-free `specialize::role_method_check` check-stage owner to produce
  `SourceDiagnostic`; the run path still reports `SpecializeError`.

## Reporting gaps

If you hit a behavior that is not on this matrix, or one that is marked ✅
but does not work in your case, that is useful to know. The intended path
is to capture a small reproducible Yulang snippet and either:

- Open a GitHub issue with the snippet and the inferred / runtime output.
- Drop it under `notes/diagnostics/` as a dated bad-snippet note.

The more reproducible the snippet, the easier it is to convert into a
fixture once Yulang-facing test fixtures land.
