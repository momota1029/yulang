# Yulang Todo

This is a local working note. It is intentionally short-lived and should be
updated as the project direction changes.

## Current Direction

Yulang now has a public repository, a working playground, and examples that show
the language's main shape. The next goal is to make the language easier to try,
debug, trust, and connect to ordinary host capabilities.

## Priority 1: Host Communication

Goal: let Yulang programs communicate with the outside world without making
effects feel like a special `perform` subsystem.

The design direction:

- User code calls ordinary functions such as `print`, `println`, `read_line`,
  `now`, `random`, or later `fetch`.
- Those functions are library-facing effect operations.
- The VM reports unhandled operations as structured host requests.
- CLI / Wasm / playground decide how to service or reject those requests.
- User-facing examples should not print raw `request ... blocked=...` output
  unless the example is intentionally demonstrating unhandled effects.

First capability set:

- Console output:
  - `print` / `println` for strings and values that implement display-like
    roles.
  - CLI writes to stdout.
  - Playground appends to an output pane.
- Console input:
  - `read_line` as an effectful request.
  - CLI can start with queued input or a clear "input unsupported" diagnostic.
  - Playground can expose a pending input prompt later.
- Time/random:
  - Add only after console output is stable.
  - Keep deterministic test hooks so examples stay reproducible.
- HTTP/file/process:
  - Keep parked for now. They need a capability policy and playground story.

Immediate tasks:

1. Add a small `std::console` act with `print` / `println`.
2. Teach CLI/Wasm host code to handle console output requests instead of
   formatting them as unexpected raw requests.
3. Add CLI, VM, and Wasm tests that run a tiny program and capture output.
4. Add one short example that uses console output.
5. Add an unhandled-effect diagnostic for unsupported host requests.

Non-goals for the first slice:

- No general FFI.
- No filesystem access.
- No network access.
- No host capability object model.
- No async runtime design beyond preserving continuations already carried by
  `VmRequest`.

## Priority 2: Error Messages

Goal: when a playground visitor writes a broken program, the compiler should
point to the right place and say what went wrong in language-level terms.

- Parser errors should identify the unexpected token and nearby expected forms.
- Type errors should name the surface expression, not only internal variables.
- Role resolution failures should say which role/method was searched for.
- Method/field errors should distinguish missing field, missing method, and
  ambiguous role method.
- Effect errors should explain unhandled effects and handler mismatch.
- Runtime lowering errors should not leak "residual polymorphic runtime IR" to
  ordinary users without a higher-level explanation.
- Playground diagnostics should show line/column and a compact code frame.

Useful first tests:

- missing `else` / broken indentation
- unknown variable
- `1 + true`
- missing method such as `1.foo`
- unhandled `console::read()`
- bad handler arm payload
- polymorphic value that runtime cannot monomorphize

## Priority 3: Stabilize Examples

Goal: examples are the public contract while the language is experimental.

- Keep every playground example runnable from CLI.
- Mirror important examples into VM/source tests.
- Add one small example for each public-facing feature before expanding docs.
- Prefer short examples over one huge demo.
- Track examples that infer but do not run as bugs, not documentation caveats.

Current key examples:

- Tour
- Struct
- Optional Args
- References
- List Update
- Sub Return
- Nondet List
- Nondet Once
- Junction
- Types
- Effects
- Console Output

## Priority 4: Partial Compilation / Std Cache

Goal: make playground runs fast enough that small edits do not feel like a full
compiler restart.

Current shape:

- Wasm `RunOutput.timings` reports phase timings for source loading, infer
  lowering, type rendering, diagnostics, core export, runtime lowering,
  monomorphize, VM compile, and VM eval.
- Playground timing output is currently sent to the browser console, not the
  visible result pane.
- Source loading now records `SourceOrigin::{Entry, Std, User}` so std and user
  code are separated at the source-set boundary.
- Wasm has a process-local lowered-std cache. The playground warms the bundled
  std cache after the first run, and later runs report `source_cache_hits` /
  `source_cache_misses` in `RunOutput.timings`.
- This cache is not yet a build-time persistent artifact. It still stores a
  cloned `LowerState` in memory after wasm startup.

Next steps:

- Design a persistent bundled std artifact for wasm startup:
  - first target: a compact `StdInferSnapshot`, not serialized whole
    `LowerState`;
  - include module/name tables, resolved refs, exported public schemes,
    syntax exports, role/impl lookup tables, effect metadata, principal bodies
    and evidence needed by export/runtime;
  - make def ids / type vars / frozen scheme ids importable without collision
    with user code;
  - keep a version/hash key based on std source text, compiler snapshot version,
    and relevant feature flags.
- Use the process-local lowered-std cache as the behavioral oracle while
  designing the persistent artifact.
- Measure first playground run separately from second run. The persistent cache
  should reduce first-run `infer_lower_ms` and ideally make type rendering /
  export cacheable later.
- Keep deeper timing available locally:
  - `--infer-phase-timings`
  - `--runtime-phase-timings`
  - `YULANG_EXPORT_TIMING=1`
- After the infer snapshot is stable, consider persistent core/export artifacts
  for std public bindings and principal evidence. Do not serialize debug-only
  derived evidence into the hot artifact unless a consumer needs it.
- Avoid treating the current global clone of `LowerState` as the final answer.
  It is a stepping stone and measurement baseline, not the long-term cache
  format.

## Priority 5: Refactoring

Goal: reduce places where one change requires touching unrelated modules.

- Split diagnostic construction from inference/lowering logic.
- Keep playground sample data separate from DOM wiring if it grows again.
- Audit duplicate "export to core IR" helper code around ref projections.
- Keep monomorphization responsibilities separate from effect/thunk lowering.
- Move hot-path ad hoc rules behind named passes with clear inputs/outputs.
- Keep host request formatting and host request handling out of core VM
  evaluation logic when possible.

## Priority 6: Language Semantics Still Needing Work

Goal: finish semantics that are visible and likely to become examples/docs.

- Optional records:
  - default evaluation order
  - interaction with subtyping
  - runtime behavior for missing fields
  - error messages for bad patterns
- References:
  - nested projections such as `&xs[0].field`
  - string index update, if intended
  - clearer explanation of `$x` and `&x`
- Effects:
  - handler type examples
  - unhandled effect diagnostics
  - hygiene/id stack documentation
- Host communication:
  - console output semantics
  - input request continuation behavior
  - deterministic testing hooks for time/random
  - host capability policy for playground
- Runtime:
  - remove remaining internal errors from user-facing paths
  - keep list/tree/string runtime behavior documented by tests

## Priority 7: Public Docs

Goal: make the repo understandable without reading implementation notes.

- README should stay short and point to playground, examples, overview.
- Overview should describe what works today, not future intent.
- Add a diagnostics page once error messages improve.
- Add a "known limitations" section that is honest but not discouraging.
- Add a short "host effects" page after console output lands.

## Suggested Next Step

Use the current playground cache timings to move from process-local std caching
to a persistent bundled std infer snapshot.

Concrete first task:

1. Write down the exact fields of `LowerState` that user lowering needs from
   std after std lowering has completed.
2. Split those fields into a small `StdInferSnapshot` structure and an
   `instantiate_std_snapshot` import path.
3. Add a test that compares uncached lowering, process-local cache lowering,
   and snapshot-instantiated lowering on a tiny program.
4. In wasm, replace warm-lowered-std cache construction with loading the
   bundled snapshot once the snapshot path is equivalent.
5. Keep diagnostics work in parallel, but do not let diagnostics add more CST
   rescans on the hot path.
