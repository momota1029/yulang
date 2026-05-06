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
- A first std `SourceFile` cache attempt was reverted after measurement. Source
  loading was not the dominant cost; infer/export/monomorphize are the current
  bottlenecks.

Next steps:

- Use the timings to confirm whether the remaining fixed cost is infer/lower,
  core export, runtime lower, monomorphize, or VM eval.
- Keep deeper timing available locally:
  - `--infer-phase-timings`
  - `--runtime-phase-timings`
  - `YULANG_EXPORT_TIMING=1`
- Split std from user code at the infer/export boundary only after the timing
  data justifies it.
- Treat a reusable std infer artifact as a real partial-compilation boundary:
  def ids, type vars, role tables, syntax exports, and principal evidence must
  have an explicit import/instantiation story before reuse.
- Avoid a quick global clone of `LowerState` as the final answer. It may help as
  a measurement step, but the long-term cache should expose a small artifact,
  not a copy of the whole compiler state.

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

Use the playground timing breakdown to choose the next partial-compilation
boundary. Console output is now available, so the immediate performance work is
to make the fixed std cost visible and then shrink it.

Concrete first task:

1. Compare first and second playground runs using `RunOutput.timings`.
2. If `source_set_ms` remains meaningful, avoid rebuilding syntax tables for
   cached std files.
3. If `infer_lower_ms` dominates, design a std infer artifact with explicit
   imported def/type-var namespaces.
4. If runtime lower / monomorphize dominates, continue shrinking fallback
   monomorphize rather than expanding source-level caching.
5. Keep diagnostics work in parallel, but do not let diagnostics add more CST
   rescans on the hot path.
