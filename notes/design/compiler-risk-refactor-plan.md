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

### 2026-05-01: Monomorphization progress made explicit

- Added `MonoStep` / `MonoProgress` to the pipeline runner.
- `rewrite-uses` now reports:
  - rewritten root expressions
  - rewritten binding bodies
  - newly created specializations
- The stabilization loop now stops from pass progress rather than a whole-round
  `Module` equality check.
- `YULANG_DEBUG_MONO_PIPELINE` now prints progress details, not only before/after
  binding and root counts.

New risk noticed:

- Several passes still derive progress by comparing their input and output
  module.  That is centralized now, but the next cleanup should make the hot
  passes report their own local changes directly, especially type refinement and
  residual role resolution.

### 2026-05-01: Type refinement reports local progress

- Kept the public `refine_module_types` API unchanged.
- Added an internal `refine_module_types_with_report` path for the
  monomorphization pipeline.
- `refine-types` now reports changed bindings and roots while it rewrites them,
  instead of cloning and comparing the full module in the pipeline wrapper.

New risk noticed:

- `RefineRewriter` still rewrites and refines many syntactic forms in one
  visitor.  A later split should separate plain substitution, expected-type
  propagation, thunk forcing, and cast insertion so each rule has a smaller
  surface.

### 2026-05-01: Residual role pass reports local progress

- `resolve-residual-role-methods` now reports changed roots, changed bindings,
  and newly emitted specializations directly.
- The stabilization loop now gets explicit progress from all passes that are
  most likely to run repeatedly: `rewrite-uses`, `refine-types`, and residual
  role method resolution.

New risk noticed:

- Residual associated binding resolution still uses wrapper-level module
  comparison.  It is outside the stabilization loop, so it is less urgent, but
  it should still get a direct report if it starts participating in fixed-point
  behavior.

### 2026-05-01: Refinement cast and thunk forcing split out

- Split runtime type-refinement cast insertion into `refine/cast.rs`.
- Split protected thunk forcing into `refine/thunk_force.rs`.
- Kept `refine/rewrite.rs` focused on traversal and syntax-directed expected
  type propagation.

New risk noticed:

- The `expr` visitor still computes the initial refined expression type inline.
  That logic is where local variables, binding types, constructor expectation,
  and expected-type propagation meet.  It should be extracted next before
  changing any rule around function arguments or handlers.

### 2026-05-01: Refinement type context split out

- Moved initial expression type selection into `refine/type_context.rs`.
- The priority order is now named in one place:
  - nullary constructor expected by context
  - local variable type
  - known binding type
  - expected type propagation when compatible
- This keeps the main expression visitor focused on syntax traversal.

New risk noticed:

- The same binding/local priority also exists in nearby monomorphization
  rewrite code.  It is not identical, but the two rules should be compared
  before changing method resolution or constructor handling again.

### 2026-05-01: Refinement pattern and statement visitors split out

- Moved pattern refinement into `refine/pattern.rs`.
- Moved statement refinement into `refine/stmt.rs`.
- `refine/rewrite.rs` now has a clearer role: module/binding/expression
  traversal plus expression-form-specific rewrites.

New risk noticed:

- Record pattern defaults can call back into expression refinement.  That is
  correct today, but optional-record work should keep this path in mind because
  defaults are not a purely pattern-local concern.

### 2026-05-01: Runtime lowering thunk helpers split out

- Created `lower/thunk.rs`.
- Moved the main thunking helpers there:
  - `prepare_expr_for_expected`
  - `finalize_effectful_expr`
  - `finalize_handler_expr`
  - `attach_forced_effect`
  - `attach_expr_effect`
  - `add_id_to_created_thunks`
  - `add_id_with_peek_if_needed`
  - `contains_peek_add_id`
- Moved effect-operation effect construction into `lower/effects.rs`, keeping
  operation-effect extraction separate from thunk wrapping.

New risk noticed:

- `apply_param_allowed_effect` still lives in `lower/function.rs`, although it
  creates thunk parameter types.  It should move into `lower/thunk.rs` with the
  rest of the thunk-boundary rules.

### 2026-05-01: Parameter allowed-effect thunking moved

- Moved `apply_param_allowed_effect` into `lower/thunk.rs`.
- Moved its direct helpers too:
  - `allowed_effect_for_param`
  - `returns_thunk`
  - `empty_row`
- `lower/function.rs` now keeps function-shape utilities instead of owning
  parameter thunk construction.

New risk noticed:

- `protect_function_body` still lives as a `Lowerer` method in `lowerer.rs`.
  Its body is now small, but it is still the place where function boundaries
  introduce hygiene administration.  That boundary should get a dedicated test
  or a named helper before changing effect hygiene again.

### 2026-05-01: Thunk lowering contract documented

- Added a module-level contract to `lower/thunk.rs`.
- The contract states when lowering may:
  - wrap a value as `Thunk`
  - force a thunk with `BindHere`
  - attach forced expression effects
  - add `AddId[peek, effect]`
  - skip administrative thunks for pure effects

New risk noticed:

- This contract now exists for lowering, but `preserve_runtime_thunk_shape` in
  monomorphization still has no local contract tying it back to lowering.  It
  should be documented or moved next so preservation does not look like creation.

### 2026-05-01: Monomorphization thunk preservation isolated

- Created `monomorphize/thunk_shape.rs`.
- Moved `preserve_runtime_thunk_shape` out of general normalization.
- Documented that this helper preserves thunk boundaries introduced by runtime
  lowering; it must not be treated as a second thunk-creation mechanism.
- Added tests for:
  - preserving a body-side thunk around a compatible scheme value
  - keeping a non-empty body effect when a refreshed scheme effect is empty
  - recursively preserving parameter and return thunks in function types

New risk noticed:

- Thunk preservation currently depends on `hir_type_compatible` both ways for
  the value shape.  That is acceptable as a preservation gate, but future
  changes to compatibility could accidentally broaden thunk preservation.  Keep
  this test set close to any compatibility refactor.

### 2026-05-01: Hygiene formatter started

- Added `crates/yulang-runtime/src/hygiene.rs`.
- Exposed:
  - `format_hygiene_expr`
  - `format_hygiene_module`
- The formatter shows:
  - `LocalPushId` scopes
  - `AddId[peek, effect]`
  - `PeekId` / `FindId`
  - handler consumed effects and residual effect summary
- Added tests that lock the output for local id scopes and handler summaries.

New risk noticed:

- This is currently a library helper, not a CLI flag.  It makes tests and
  debugging possible, but the next step should expose it through the CLI or
  runtime debug path so failing examples can print hygiene without ad hoc code.

### 2026-05-01: Hygiene formatter exposed in CLI

- Added `--hygiene-ir` to the `yulang` CLI.
- The flag lowers and monomorphizes runtime IR, then prints the focused hygiene
  view from `runtime::format_hygiene_module`.
- Verified it on `examples/01_struct_with.yu`.

New risk noticed:

- The hygiene output currently includes generic structural lines such as
  `apply` and `lambda`, which are useful for nesting but still noisy.  If this
  becomes hard to read on real handler examples, add a compact mode that prints
  only hygiene operations plus path breadcrumbs.
