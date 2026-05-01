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

### 2026-05-01: Residual polymorphic diagnostics name the source

- Split residual polymorphic runtime errors by source:
  - remaining binding type parameters
  - remaining runtime body, scheme, or role-requirement variables
- Updated the error message to say where the residual variable was found.
- Added a display test for the new message.

New risk noticed:

- The diagnostic still prints raw `TypeVar("a")` debug output.  That is enough
  for compiler debugging, but user-facing diagnostics should eventually render
  these variables with the same compact formatter used by inferred types.

### 2026-05-01: Runtime phase timings exposed

- Added `--runtime-phase-timings` to the `yulang` CLI.
- The flag reports:
  - runtime lowering
  - monomorphization
  - VM compile, when `--run` is used
  - VM eval, when `--run` is used
- Verified it with `examples/01_struct_with.yu`.

New risk noticed:

- The timing output is still ad hoc text.  For guardrails, this should later
  become a reusable profile object or snapshot command so examples can be
  compared across commits.

### 2026-05-01: Monomorphization profile exposed

- Added `monomorphize_module_profiled`.
- Added public profile structs for:
  - pass count
  - per-pass binding/root counts
  - per-pass progress
  - generated specialization count
- `--runtime-phase-timings` now reports monomorphization pass count and total
  generated specializations.

New risk noticed:

- The top-level pipeline still has fixed initial repeated rewrite/refine passes
  before the stabilization loop.  The profile now makes that visible, but a
  later pass should convert the whole pipeline into a smaller fixed-point driver
  instead of keeping both approaches.

### 2026-05-01: Residual type variables render compactly

- Updated residual polymorphic runtime diagnostics to print type variables as
  `a, b` instead of Rust debug output like `TypeVar("a")`.
- Kept the diagnostic source added in the previous pass.

New risk noticed:

- Runtime diagnostics and infer diagnostics still use separate formatting code.
  A shared small formatter for paths, type variables, and common type fragments
  would reduce future drift.

### 2026-05-01: Monomorphization pipeline stages introduced

- Replaced the single flat pass list with `MonoStage`.
- The pipeline now distinguishes:
  - bounded repeat warmup for early rewrite/refine
  - fixed-point role specialization
  - fixed-point final cleanup
  - one-shot cleanup passes
- Kept the early warmup bounded to avoid generating unreachable specializations
  before pruning.
- Verified `examples/01_struct_with.yu` still generates 11 specializations and
  runs successfully.

New risk noticed:

- The early warmup is still a bounded repeat rather than a true fixed point.
  That is intentional for now because full fixed-point specialization can grow
  unreachable bindings before pruning.  The next cleanup should make
  specialization progress distinguish reachable from unreachable output.

### 2026-05-01: Rewrite pass skips unreachable specializations

- `rewrite-uses` now recomputes reachability each internal round.
- Added specialized bindings are only rewritten when they are reachable from
  roots or root expressions.
- This avoids spending work on specialization chains that pruning would later
  discard.
- Verified `examples/01_struct_with.yu` still runs and keeps the same generated
  specialization count.

New risk noticed:

- Reachability is recomputed inside the rewrite loop.  That is simple and safer
  than rewriting every generated binding, but it may be worth caching adjacency
  if large examples show this becoming hot.

### 2026-05-01: Unknown type meanings named

- Added named helpers for the main remaining `Any` meanings:
  - inference holes, where `Any` and principal vars are both incomplete
  - runtime projection fallback, where only `Any` means "erased fallback"
  - wildcard effect annotations, which are still represented as `Any`
- Kept the representation unchanged and routed existing hole helpers through
  the explicit names.
- Replaced a few direct `Any` constructions in thunk lowering and runtime
  projection with the named constructors.

New risk noticed:

- The representation is still shared.  This makes the code easier to audit, but
  it does not yet prevent a caller from passing a wildcard effect into a value
  position.  The next step should narrow more direct `Type::Any` use sites or
  add boundary checks where runtime execution begins.

### 2026-05-01: Strict runtime value-type audit added

- Added an opt-in strict runtime value-type checker.
- It currently rejects the two places where the VM really uses type witnesses
  operationally:
  - thunk value types
  - cast/coerce source and target types
- Kept the checker out of normal VM compilation for now.

New risk noticed:

- Enabling the strict checker globally exposed real residual `_` in existing
  generated IR, especially loop handler thunks and nondeterminism continuation
  queues.  Those examples still run because the current VM mostly erases type
  metadata, but they are not ready for a fully typed VM boundary.  The next
  cleanup should eliminate those residuals by improving specialization, not by
  weakening the strict check.

### 2026-05-01: Demand-driven monomorphization plan started

- Added a separate plan for replacing the current fixed-point monomorphizer
  with a demand-driven algorithm.
- Started `monomorphize2` beside the old implementation.
- First slice:
  - `DemandQueue`
  - `Demand`
  - `DemandKey`
  - `DemandSignature`
- Demand signatures now convert `Any` in value and effect slots into
  monomorphization holes instead of treating `Any` as a runtime type witness.

New risk noticed:

- This is only the demand-key layer.  The next step must add the body checker
  skeleton, otherwise this will remain a clean wrapper around the old problem
  rather than a replacement for the fixed-point rewrite loop.

### 2026-05-01: Direct-call demand collection started

- Added `DemandCollector` to `monomorphize2`.
- The collector builds a registry of generic bindings and walks root /
  monomorphic binding bodies.
- Direct calls to generic bindings now enqueue a demand of the shape
  `arg_type -> result_type`.
- Added tests for:
  - direct generic calls enqueueing one demand
  - monomorphic calls being ignored

New risk noticed:

- This only handles the simple `f x` shape.  Curried calls such as `f x y`,
  role calls, constructor calls, and effect operations need explicit demand
  rules rather than being recovered by recursive tree rewrites.

### 2026-05-01: Curried direct-call demands added

- Extended `DemandCollector` to recognize applied call chains.
- A call such as `f x y` now enqueues one demand shaped like
  `x_type -> y_type -> result_type`.
- The collector avoids enqueuing an extra partial-application demand for the
  inner `f x` in this direct generic-call case.

New risk noticed:

- The collector still only sees demand shapes already present in runtime IR.
  The next layer must instantiate generic schemes with fresh monomorphization
  holes and check the body, otherwise `_` inside a binding's own annotation will
  not be solved by local body information.

### 2026-05-01: Demand-hole unifier started

- Added `DemandUnifier` and `DemandSubstitution`.
- It solves demand holes without turning them back into `Any`.
- Value/core/effect holes have separate substitution maps, so an effect wildcard
  cannot accidentally become a value witness.
- Added tests for:
  - function value holes solved by concrete argument/result types
  - effect holes solved only in the effect substitution map

New risk noticed:

- This unifier is still structural and intentionally small.  It does not yet
  understand subtyping, role requirements, row reordering, or `never <: unit`.
  Those rules should be added as explicit solver rules, not by falling back to
  whole-tree rewrite passes.

### 2026-05-01: Demand checker skeleton started

- Added `DemandChecker` beside the fixed-point monomorphizer.
- The checker currently handles:
  - literals
  - local variables
  - lambda checking against an expected function demand
  - simple application checking
- Lambda body checking can now solve a return hole from the body itself.  For
  example, a demand shaped like `unit -> _` over a lambda returning `int` solves
  to `unit -> int`.

New risk noticed:

- The checker still falls back to existing expression type witnesses for
  unsupported syntax.  This is fine for the skeleton, but it must not become the
  long-term behavior.  The next steps should add explicit rules for block,
  tuple, if/match, thunk/bind, and direct generic call demand emission inside
  checked bodies.

### 2026-05-01: Checked bodies emit child demands

- `DemandChecker` now knows which bindings are generic.
- When a checked body calls a generic binding directly, the checker enqueues a
  child demand instead of rewriting the call.
- Curried child calls are represented as a single demand signature, just like
  root-level direct calls.
- Added a test where checking `use_id x = id x` emits the child demand
  `id : int -> int`.

New risk noticed:

- Child demands are only collected; they are not processed by a driver yet.
  The next step should add a small deterministic `DemandEngine` loop that pops
  a demand, checks it, appends child demands, and records checked outputs.

### 2026-05-01: Demand engine loop started

- Added `DemandEngine`.
- It initializes the queue from `DemandCollector`, then repeatedly:
  - pops one demand
  - checks it with `DemandChecker`
  - appends child demands emitted by the checked body
  - records the checked result
- Added a test where root demand collection reaches `id` through a monomorphic
  helper body.

New risk noticed:

- The engine currently records checked demand metadata only.  It does not emit
  specialized bindings yet.  The next step should add a specialization table
  keyed by `DemandKey` and produce deterministic specialized paths before
  rewriting call sites.

### 2026-05-01: Demand specialization table added

- Added `SpecializationTable`.
- Each checked demand now receives a deterministic specialized path such as
  `id__ddmono0`.
- The table is keyed by `DemandKey`, so repeated identical demands reuse the
  same specialized path.
- `DemandEngineOutput` now includes the checked demand list and the planned
  specializations.

New risk noticed:

- The specialization table is metadata only.  The next step should create
  actual `Binding` values with substituted runtime types, then make call-site
  rewriting a targeted replacement from `DemandKey` to specialized path rather
  than a full tree fixed-point pass.

### 2026-05-01: Demand specialized binding emission started

- Added `DemandEmitter`.
- The emitter turns a solved demand signature back into a runtime HIR type and
  rejects unresolved value/core/effect holes instead of materializing `Any`.
- Specialized bindings now:
  - receive deterministic `__ddmonoN` paths from the specialization table
  - clear type parameters and role requirements
  - get a runtime-preserving scheme body
  - retag lambda locals from the solved demand signature
- Direct generic child calls are rewritten by exact `DemandKey` lookup, not by
  repeated whole-tree refinement.
- Fixed an important early bug: child demand signatures must use the type known
  from the checking context, such as a lambda parameter solved to `int`, rather
  than the original `Any` witness stored on the argument expression.

New risk noticed:

- Body emission still has fallback paths for syntax that the demand checker does
  not understand yet.  The next step should make block/if/tuple/thunk/bind/catch
  checking produce explicit expected signatures so emission does not need to
  trust stale expression annotations.

### 2026-05-01: Demand checker hole allocation made local to checking

- Added `DemandSignature::from_runtime_type_with_holes`.
- Demand signatures can now continue hole numbering from an existing expected
  signature instead of restarting at hole `0`.
- `DemandChecker` now allocates fresh holes through one checker-local counter
  while checking a demand.
- Child demand signatures now use context-solved argument signatures even when
  the original argument expression still carries an `Any` annotation.

New risk noticed:

- Hole allocation is now sane within one checked demand, but `DemandKey`
  equality still depends on syntactic hole numbers for partially unknown
  demands.  Before wiring this path into real compilation, keys with holes
  should be canonicalized so equivalent unknown shapes deduplicate reliably.

### 2026-05-01: Demand checker learned block, tuple, and if

- Added explicit demand-checking rules for:
  - block statements and tail expressions
  - simple `let` bindings with local variable introduction
  - tuple item synthesis
  - `if` branch checking / branch unification
- Added tests where stale `Any` annotations on local variables are ignored in
  favor of context-derived demand signatures.

New risk noticed:

- Pattern support in block `let` is intentionally narrow and only binds simple
  names.  Record/list/tuple patterns need their own local-introduction rules so
  destructuring does not fall back to old expression annotations.

### 2026-05-01: Demand keys canonicalize holes

- `DemandKey` now canonicalizes value/core/effect holes before entering the
  queue or specialization cache.
- Equivalent partially unknown demand shapes deduplicate even if they were
  produced with different local hole ids.
- Value, core, and effect holes are still canonicalized in separate namespaces,
  so an effect wildcard cannot be confused with a value wildcard.

New risk noticed:

- Canonicalization only solves cache identity.  The checker still needs
  language-aware rules for subtyping and effect rows so two semantically equal
  rows with different ordering or representation do not split into separate
  specializations.

### 2026-05-01: Demand checker learned thunk, bind, and handle basics

- Added explicit checking rules for:
  - `Thunk`: checks the inner expression against the thunk value demand
  - `BindHere`: checks the forced expression as a thunk whose value is the
    expected result demand
  - `Handle`: checks handler arms against the expected result demand and binds
    value-arm payloads from the handled body value
  - `LocalPushId`, `AddId`, `Coerce`, and `Pack`: forward demand to their body
    where that is semantically transparent for the current skeleton
- Pattern-local introduction now passes `DemandSignature` values directly
  instead of converting value holes into core holes.

New risk noticed:

- Handler checking is still structural.  It does not yet subtract consumed
  effects or validate resume effects with the full handler hygiene model.  That
  should be added as explicit effect-row solving, not inferred from handler
  names.

### 2026-05-01: Demand checker learned records, selection, variants, and match

- Added explicit checking/synthesis for:
  - record literals
  - field selection from synthesized record demand
  - variant construction
  - match arms with pattern-local bindings
- Added tests where record selection and variant match payloads recover `int`
  from context even though intermediate expressions carry stale `Any`.

New risk noticed:

- Record spread and open rows are still only traversed, not solved.  Optional
  records will need a real row-demand rule so missing/default fields are handled
  by the same algorithm rather than by post-hoc expression repair.

### 2026-05-01: Demand unifier learned unordered effect rows

- Effect rows now unify independent of item ordering.
- Singleton rows can unify with plain effect atoms.
- Effect holes inside a closed row can be solved by matching remaining row
  items.

New risk noticed:

- This is still a closed-row rule.  Open effect rows and effect subtraction for
  handlers need a dedicated representation of residual row variables; otherwise
  handler typing will drift back toward ad-hoc repair.

### 2026-05-01: Demand unifier gained occurs checks

- Added occurs checks for value, core, and effect holes.
- Binding a hole to itself is a no-op, but binding it to a shape that contains
  itself now fails with an explicit namespace-tagged error.
- This protects the new solver from turning a bad demand into recursive
  substitution and stack overflow.

New risk noticed:

- The substitution applier still assumes stored substitutions are acyclic.  The
  occurs check should preserve that invariant, but debug invariant tests should
  eventually assert it directly for imported or constructed substitutions.

### 2026-05-01: Demand monomorphization wired into the pipeline

- Added a public `demand_monomorphize_module` entrypoint.
- The demand path now:
  - runs the demand engine
  - emits specialized bindings
  - rewrites root and monomorphic binding call sites to specialized paths
  - appends emitted `__ddmonoN` bindings to the runtime module
- Added a `demand-specialize` monomorphization pass at the start of the normal
  runtime monomorphization pipeline.
- The pass is currently best-effort: if demand checking/emission fails, or if
  the produced module fails validation, the old pipeline continues from the
  original module.
- Added a test proving a root call to a generic binding is rewritten to its
  demand-specialized binding.

New risk noticed:

- The pass is connected but not yet authoritative.  The fallback is necessary
  because optional record rows, handler effect subtraction, references, and a
  few nominal/variant shapes still need explicit demand rules.  Removing the
  fallback should be the milestone that proves the replacement is complete.

### 2026-05-01: Demand unifier learned structural records and variants

- Added core demand rules for:
  - `never` as a bottom value
  - records unified by field name rather than field order
  - variants unified by case name rather than case order
- These rules remove several early false failures from the connected
  `demand-specialize` pass.

New risk noticed:

- Nominal self types can still appear as records in actual runtime bodies.
  That needs a principled bridge from nominal runtime type information to the
  structural body shape rather than a one-off named-vs-record exception.
