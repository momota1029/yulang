# Yulang Compiler Risk Refactor Plan

This is a working plan for reducing fragile compiler/runtime behavior.  It is
not a feature roadmap.  The goal is to make the implementation harder to break
when adding language features such as references, handlers, optional records,
and new playground examples.

## 0. Current Risk Summary

The most dangerous area is not one isolated bug.  It is the chain:

1. source lowering infers principal information
2. export turns it into core IR
3. runtime lowering projects core types into runtime HIR types
4. monomorphization repeatedly rewrites and refines runtime IR
5. VM erases and executes the result

Several recent fixes had to pass information through this whole chain.  That is
the main risk.  A local rule in one step can be accidentally erased or widened
by a later step, especially around `Thunk`, `Any`, effect rows, and handler
hygiene.

The highest-risk symptoms are:

- `Any` / `_` accidentally becoming a real runtime shape.
- `Thunk` insertion being recovered later by shape matching instead of an
  explicit contract.
- monomorphization depending on repeated rewrite/refine passes until the result
  happens to settle.
- effect handler hygiene depending on runtime behavior that is hard to inspect.
- synthetic reference helpers being copied/lowered differently from their
  source definitions.
- user-facing diagnostics receiving internal errors such as residual
  polymorphic bindings.

## 1. Refactor Principles

- Each pass should have one stable input and one stable output invariant.
- When a pass adds semantic information, later passes must not need to rediscover
  it from syntax or display types.
- `Any` should be treated as "unknown for recovery" only at narrow boundaries,
  never as a normal runtime type.
- `Thunk[effect, value]` should be represented as runtime semantics, not as a
  formatting consequence of function effect slots.
- Monomorphization should be a fixed-point engine with explicit pass ordering
  and progress checks, not a hand-written list of repeated rewrites.
- Tests should check invariants at pass boundaries, not only final VM output.

## 2. Phase 1: Map And Lock Pass Boundaries

Goal: make every compiler stage state what it promises.

Tasks:

- Add a short module-level contract to:
  - `crates/yulang-infer/src/export/mod.rs`
  - `crates/yulang-runtime/src/lower/mod.rs`
  - `crates/yulang-runtime/src/monomorphize/mod.rs`
  - `crates/yulang-runtime/src/refine/mod.rs`
  - `crates/yulang-runtime/src/validate/mod.rs`
  - `crates/yulang-runtime/src/vm/erase.rs`
- Add a debug-only or test-only invariant check after each runtime stage:
  - no non-runtime type constructors after runtime lowering
  - no residual principal variables after monomorphization
  - no `Any` in executable value positions before VM erase
  - every `catch` body that may handle an effect is a thunk
  - every `AddId` wraps a thunk
  - every `LocalPushId` scope is explicit in the runtime IR
- Split "diagnostic type" conversion from "runtime type" conversion.  Today
  `diagnostic_core_type` and runtime-preserving conversions are easy to confuse.

Suggested first commit:

- Create `runtime/src/invariant.rs`.
- Wire it after `lower_core_program`, after `monomorphize_module`, and before
  `compile_vm_module` in tests.
- Keep checks narrow and make failures print the binding/root path.

## 3. Phase 2: Tame `Any`, Hole, And Runtime Type Projection

Goal: prevent `_`/`Any` from becoming a hidden control signal.

Risk:

Recent bugs came from whether `Any` means "unknown value", "wildcard effect",
"lost principal type", or "acceptable erased runtime value".  These meanings
must be split.

Tasks:

- Introduce small wrapper enums or helper names for the four meanings:
  - unknown source type
  - principal hole
  - wildcard effect annotation
  - erased runtime fallback
- Rename helpers so intent is visible:
  - `diagnostic_core_type`
  - `runtime_core_type`
  - `project_runtime_type_with_vars`
  - `project_runtime_hir_type_with_vars`
- Add tests that fail if a wildcard parameter effect is erased across:
  - lower binding
  - monomorphization refresh
  - VM erase
- Add negative tests showing that ordinary polymorphic effect variables do not
  become `Thunk[⊤, ...]` everywhere.

Exit condition:

- A reviewer can tell from function names whether a conversion is for display,
  runtime execution, or inference simplification.

## 4. Phase 3: Replace Monomorphization Loop With A Worklist

Goal: stop depending on a fixed sequence of repeated rewrite/refine calls.

Current smell:

`monomorphize_module` calls rewrite/refine/refresh several times by hand.  This
works, but it hides which pass produced progress and which invariant each pass
needs.

Tasks:

- Define a `MonoPass` enum and a `MonoPipeline` runner.
- Each pass reports:
  - changed binding count
  - changed root count
  - new specializations
  - residual polymorphic bindings
  - residual role calls
- Run passes until no progress or until a small hard limit is hit.
- When the limit is hit, report the last pass that made progress and the first
  remaining residual.
- Keep pass order explicit, for example:
  - specialize direct calls
  - refine body types
  - refresh closed schemes
  - canonicalize equivalent specializations
  - inline nullary constructors
  - resolve residual role calls
  - prune unreachable bindings
  - validate

Exit condition:

- Adding one pass should not require copying the whole pass sequence in several
  places.
- A residual polymorphic failure should tell which pass stopped making progress.

## 5. Phase 4: Separate Thunk Lowering From Type Repair

Goal: make `Thunk` introduction explicit and stop recovering it later.

Risk:

The current runtime lowerer can introduce thunks from expected types, parameter
annotations, function allowed effects, tuple/if/block effects, and handler
shape.  Later monomorphization must then preserve those shapes.  This makes
small changes surprisingly wide.

Tasks:

- Create a `runtime::thunking` module or `lower/thunk.rs`.
- Move these responsibilities there:
  - `apply_param_allowed_effect`
  - `prepare_expr_for_expected`
  - `finalize_effectful_expr`
  - `protect_function_body`
  - `add_id_to_created_thunks`
  - `preserve_runtime_thunk_shape`
- Add a single document comment that states:
  - when a value becomes a thunk
  - when a thunk is forced with `bind_here`
  - when `AddId` is inserted
  - which steps are allowed to preserve but not create thunks
- Add pass-boundary tests for:
  - pure function argument stays a value
  - `x: [_] _` stays a thunk parameter
  - handler removes the handled effect from result type
  - tuple/if effects become a thunk exactly once

Exit condition:

- Monomorphization should not be the first place that decides a value was
  semantically a thunk.  It may preserve or specialize a thunk, but not invent
  one to repair earlier loss.

## 6. Phase 5: Make Effect Hygiene Auditable

Goal: make `LocalPushId`, `PeekId`, `FindId`, and `AddId` behavior inspectable.

Risk:

Effect hygiene is semantically subtle.  The VM uses a persistent guard stack,
but the compiler has to place the operations correctly.  Mistakes often pass
simple examples and fail only with copied continuations or nested handlers.

Tasks:

- Add a small runtime IR pretty mode for hygiene:
  - show `LocalPushId` scopes
  - show `AddId[peek, effect]`
  - show handler entry guard behavior
- Add VM tests for:
  - nested handlers where inner code pushes ids
  - continuation invoked twice
  - handler must use entry stack, not current stack
  - `AddId` overwrites only unprotected effects
  - allowed effect remains unmarked
- Add compiler tests checking placement:
  - function boundary wraps body in `LocalPushId`
  - `x: [effect] _` creates `AddId[peek, effect]`
  - pure arguments do not get unnecessary hygiene admin

Exit condition:

- When hygiene breaks, the failing IR should show the missing or extra id
  operation without reading VM internals.

## 7. Phase 6: References And Synthetic Acts

Goal: make `$x`, `&x`, `&p.field`, and `&xs[i]` rely on one reference model.

Risk:

Reference support crosses source lowering, synthetic act generation, export,
runtime lowering, handlers, and VM execution.  Local fixes easily break one of
field projection, index projection, or handler capture.

Tasks:

- Write a short `notes/design/references-runtime.md` with the current model:
  - local reference is a synthetic effect
  - `get` and `set` operations
  - child refs for field/index updates
  - parent update through `ref_update`
- In code, separate:
  - synthetic local ref act creation
  - child ref projection export
  - runtime lowering of reference handlers
  - VM execution of local effects
- Add one shared fixture set used by infer, runtime IR, and VM tests:
  - local read/write
  - field update
  - list index update
  - nested `&xs[0].field` when supported
  - shadowing of synthetic projection by real methods

Exit condition:

- A change to reference syntax should not require editing unrelated
  monomorphization code unless the runtime type contract changes.

## 8. Phase 7: Diagnostics As A Safety Net

Goal: turn internal failure modes into useful user-level errors.

Tasks:

- Add surface diagnostics for:
  - residual polymorphic runtime IR
  - residual `Any` before VM
  - unhandled effect request at runtime
  - expected thunk / got value
  - missing field versus missing method
- Create `examples/bad/*.yu` or test-only fixtures for broken programs.
- Make playground show the same compact diagnostics as CLI.

Exit condition:

- A public user should not see raw internal names such as `ResidualPolymorphic`
  without a sentence explaining what language-level construct caused it.

## 9. Phase 8: Performance Guardrails

Goal: avoid making HIR2-style passes slower as the language grows.

Tasks:

- Add coarse timing around:
  - source lowering
  - principal export
  - runtime lowering
  - monomorphization
  - VM compile
  - VM eval
- Add benchmark-ish smoke commands for:
  - playground tour
  - nondet once
  - list update
  - optional records
  - std preload
- Track:
  - number of monomorphization passes
  - number of generated specializations
  - largest binding body size
  - runtime IR binding count
- Fail only on severe explosions at first.  Prefer warning snapshots before
  strict thresholds.

Exit condition:

- When a small refactor doubles runtime lowering or monomorphization time, it is
  visible immediately.

## 10. Recommended Order

Do this in small commits:

1. Add runtime invariant checks and pass-boundary tests.
2. Rename/split type conversion helpers around diagnostic/runtime/projection.
3. Extract thunking helpers without changing behavior.
4. Convert monomorphization to a measured worklist.
5. Add hygiene-focused IR display and tests.
6. Consolidate reference fixtures across infer/runtime/VM.
7. Improve diagnostics for the first three internal errors users can hit.
8. Add timing counters and regression smoke commands.

## 11. First Concrete Task

Start with the smallest useful refactor:

- Create `crates/yulang-runtime/src/types/core_view.rs`.
- Move or wrap:
  - `diagnostic_core_type`
  - `runtime_core_type`
  - `strict_core_type`
  - `value_core_type`-like helpers if appropriate
- Rename call sites only where the distinction is currently dangerous.
- Add tests:
  - diagnostic conversion erases thunk effects
  - runtime conversion preserves function parameter/return effects
  - strict conversion rejects non-core runtime function values

This first task is low risk and directly protects the bug class that just
appeared around wildcard thunk preservation.

## Progress Log

### 2026-05-01: Runtime invariant checker started

- Added a dedicated runtime invariant layer separate from type validation.
- First checks:
  - `BindHere` must force a thunk.
  - `Thunk` node type must match its effect/value payload.
  - `AddId` must wrap a thunk and must not use an empty allowed effect.
  - effectful `Handle` bodies must be thunks.
- Wired the checker after runtime lowering, after monomorphization, and before
  VM erase.
- Added negative tests for malformed `BindHere`, `Thunk`, and `AddId`.

New risk noticed:

- Some invariants are semantic, not merely structural.  For example, handler
  body thunking is only required when the handler actually consumes effects.
  Future checks should keep this distinction, or they will reject valid
  value-only `catch` forms.

### 2026-05-01: Core type views split out

- Moved runtime/core conversion helpers into `types/core_view.rs`.
- Kept the distinction explicit:
  - diagnostic core view erases thunk effects
  - runtime core view preserves function parameter/return effect slots
  - strict core view is only for first-order runtime core types
- Added tests that lock the difference between diagnostic and runtime views.

New risk noticed:

- The same `core_ir::Type::Fun` shape is used both for diagnostic display and
  for runtime-preserving function effect slots.  Future refactors should avoid
  passing a bare `core_ir::Type` when the caller really needs one of these
  specific views.

### 2026-05-01: Monomorphization pass sequence named

- Replaced the hand-written top-level sequence in `monomorphize_module` with a
  named `MonoPass` pipeline.
- Kept the old pass order exactly, so this is a structure-only change.
- Added `YULANG_DEBUG_MONO_PIPELINE` output for coarse pass progress:
  binding count and root count before/after each pass.

New risk noticed:

- The current pipeline still repeats rewrite/refine/refresh by fixed count.  Now
  that each pass has a name, the next step should replace the fixed list with a
  progress-aware loop and report which pass stopped making progress.

### 2026-05-01: Monomorphization stabilization loop introduced

- Replaced the repeated late rewrite/refine/refresh/role-resolution block with
  a bounded stabilization loop.
- The loop exits when a full round makes no IR change.
- Kept a hard limit to avoid accidental infinite compiler loops.

New risk noticed:

- The loop currently compares whole `Module` values.  That is simple and safe
  for behavior, but it is not the final performance shape.  A later cleanup
  should make each pass report its own progress instead of relying on full
  structural comparison.
