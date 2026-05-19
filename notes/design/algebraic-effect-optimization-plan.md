# Algebraic Effect Optimization Plan

This note is the design boundary for optimizing Yulang's algebraic-effect
execution without treating `std::undet::each` or any other library name as a
special loop construct.

## Problem

The current native CPS path faithfully represents effect execution through
`Perform`, handler lookup, resumption allocation, return-frame snapshots,
guard-stack snapshots, and `Resume` / `ResumeWithHandler`. This is correct, but
benchmarks such as:

```yulang
(each 1..20 + each 1..20).list.say
```

spend most of their time in the generic control representation rather than in
integer arithmetic or list construction.

The tempting optimization is to recognize `each` and emit a loop. That is not
the optimization this plan accepts. If a loop-like machine appears in generated
code, it must be the result of defunctionalizing algebraic-effect control
according to the IR semantics, not of treating one library operation as syntax.

## Reading-Derived Invariants

### CPS / SSA

Kelsey and Appel give the compiler-facing view: CPS continuations can be treated
as SSA blocks when their control protocol is explicit. The key distinction for
Yulang is not "function versus loop", but:

- continuation entries that behave as local jumps;
- continuation entries that escape as resumption values;
- full call entries that require a call/return protocol;
- dominance/use information for values passed through continuation parameters.

Yulang already has `CpsContinuation`, `CpsShotKind`, `Continue`, and Cranelift
block lowering. The missing piece is a reusable region object that says which
handler/perform/resume subgraph can be lowered as a local control-flow graph.

### One-shot / Multi-shot Control

Bruggeman/Waddell/Dybvig justify the main control invariant: one-shot
continuations may be moved or reinstated without copying, while multi-shot
continuations require sharing/promotion semantics. For Yulang this means:

- `CpsShotKind::OneShot` allows destructive control-stack reuse only when no
  `CloneContinuation` or multi-shot capture can observe the move;
- `CpsShotKind::MultiShot` forbids destructive region lowering unless the IR
  explicitly materializes a cloneable state representation;
- mixed one-shot/multi-shot regions need promotion boundaries, not ad hoc
  shortcuts.

### Algebraic Handlers

Plotkin/Pretnar give the effect-specific invariant: handling is an induced
homomorphism over operation applications. In implementation terms:

- a `Perform` is not a call to a named function; it is an operation with a
  continuation;
- a handler arm is an interpretation of that operation;
- `Resume` applies the captured continuation under the same handler semantics;
- operations in the handler arm itself are outside that handler unless an
  enclosing handler catches them;
- a transformation is valid only when this operation/handler/resume structure
  is preserved.

Therefore the optimizer may inspect `CpsTerminator::Perform`, `CpsHandlerArm`,
`CpsStmt::Resume`, `CpsStmt::ResumeWithHandler`, and `CpsStmt::CloneContinuation`,
but must not inspect std paths such as `std::undet::each`.

## Proposed Pass: Effect Handler Region Analysis

Add a separate analysis module before destructive rewrites:

```text
cps_effect_regions.rs
```

Entrypoint:

```rust
pub fn analyze_effect_handler_regions(function: &CpsReprAbiFunction)
    -> Vec<EffectHandlerRegion>
```

Initial region data:

- handler id and install sites;
- operations handled by each arm;
- `Perform` sites targeting the handler;
- resume continuation id and shot kind;
- arm entry continuation id;
- resume uses inside the arm, including count and arguments;
- `CloneContinuation` uses that make the region multi-shot-sensitive;
- nested `Perform` sites in the handled body and in the arm body;
- escape/value continuations for the handler scope;
- environment values captured by install/reentry.

This pass is intentionally read-only at first. Its first job is to make the
semantics visible and testable.

## Region Classes

The pass should classify regions, from least to most optimizable:

- `Opaque`: insufficient information; keep generic runtime path.
- `SingleResume`: handler arm resumes exactly once and does not clone the
  resumption.
- `FiniteMultiResume`: handler arm resumes a known finite number of times with
  explicit arguments and does not leak the resumption.
- `EscapingResumption`: resumption is stored, returned, passed to unknown code,
  cloned, or resumed by an unknown callee.
- `NestedEffectful`: arm or resumed continuation performs operations that may be
  caught by an enclosing or sibling handler; keep ordering evidence.

`FiniteMultiResume` is the interesting class for nondeterminism. It is not
special to `each`: any handler arm with a known finite resume schedule can be
lowered to a state machine if the captured continuation and surrounding handler
stack can be represented explicitly.

## Optimization Direction

After classification, add a later rewrite/codegen path:

1. Build a local SSA/control-flow view of a region.
2. Defunctionalize resumptions into a small explicit state value or local block
   dispatch.
3. Replace repeated generic resumption allocation and stack snapshot/restore
   with region-local state transitions.
4. Preserve operation ordering by routing nested `Perform` through the same
   handler search rules as the generic runtime.
5. Fall back to the generic path for `Opaque` or `EscapingResumption`.

This can generate loop-shaped machine code, but only because the effect region
has become a finite state machine under the algebraic handler semantics.

## Non-Goals

- No `Path` or function-name special casing for `each`.
- No optimization justified by "this is pure except for nondeterminism" unless
  the IR proves the relevant effect/control boundaries.
- No destructive treatment of `MultiShot` resumptions without an explicit
  cloneable state representation.
- No Cranelift-only peephole that bypasses CPS validation.

## First Implementation Slice

1. Add `cps_effect_regions.rs` with read-only analysis and tests built from
   hand-written CPS modules.
2. Integrate region counts into `CpsOptimizationProfile` trace:
   `effect_regions`, `single_resume_regions`, `finite_multi_resume_regions`,
   `escaping_resumption_regions`, `opaque_effect_regions`.
3. Add a regression fixture for a handler arm that resumes twice and one that
   lets the resumption escape, proving classification is structural.
4. Only after the classifications are stable, add a rewrite/codegen path for
   one conservative class.

The first real rewrite target should be `SingleResume`, because it checks the
one-shot machinery and nested-effect ordering without pretending nondeterminism
is a loop. `FiniteMultiResume` should follow once escape and clone detection is
reliable.

## Current Finding: Dynamic Handler Boundary

The first analysis slice found an important boundary in
`(each 1..20 + each 1..20).list.say`.

`std::undet::undet::list__mono3` installs the nondeterminism handler and then
forces its thunk argument under that handler. The actual `Perform` sites for
`branch` / `reject` are inside `std::undet::undet::each__mono1`, where the
handler id is the dynamic-handler sentinel rather than a local handler id. A
function-local pass therefore sees those `Perform` sites as `Opaque`.

The module-level read-only pass now links this shape structurally:

```text
list__mono3 EffectfulForce under handler(branch/reject)
  -> dynamic Perform(branch/reject) in each__mono1
```

This link uses IR facts only:

- active `InstallHandler` state at an effectful boundary;
- handler arm effect paths, compared with the same suffix-style effect matching
  the runtime already uses;
- dynamic `Perform` sites in effectful callees or unknown thunk/apply bodies;
- local thunk entries created inside handler arms.

It does not inspect `std::undet::each` as a name. In the 20x20 list benchmark,
the `branch` arm is classified as `FiniteMultiResume` after following the two
local thunks it creates; those thunk entries perform the `Resume true` and
`Resume false` calls. The `reject` arm remains `Opaque` / no-resume, which is
the expected non-resuming failure branch.

The next optimization step is not to rewrite `each` into a loop. It is to
specialize the handler/thunk/callee region enough that the dynamic handler
lookup and generic resumption allocation can be replaced by a finite state
representation for this region. In practice this probably requires controlled
inlining/contification across:

- direct call returning the list thunk;
- force of the thunk under an installed handler;
- effectful call sites inside the forced thunk;
- handler arms that build local thunks containing resumes.

The second analysis slice now builds that bridge as read-only data. A dynamic
effect region plan records the concrete resume schedule:

```text
branch arm:
  thunk entry 8 -> Resume true
  thunk entry 9 -> Resume false
reject arm:
  no resume
```

It then links direct-call thunk arguments to those region plans. On the 20x20
benchmark this produces three ready specialization seeds:

```text
root_0 list(thunk entry 1): ReadyFinite(branch), no-resume(reject)
list__mono3 recursive list(thunk entry 8): ReadyFinite(branch), no-resume(reject)
list__mono3 recursive list(thunk entry 9): ReadyFinite(branch), no-resume(reject)
```

These call sites originally had `post_call_force_chain=2`: the direct call
returned a thunk-shaped surface for the caller, and the caller immediately
forced it twice before using the list value. The CPS optimizer now collapses
consecutive deep `ForceThunk` statements, so the same seeds report
`post_call_force_chain=1`. This is a generic IR simplification: `ForceThunk`
already peels nested thunks until a non-thunk value is reached in both the
evaluator and native runtime.
The optimizer also removes a `ForceThunk` of a structurally known non-thunk
value when every use of the force result is in the same continuation tail, so
the 20x20 optimized statement count now drops from 353 to 298 before any
handler-specific destructive rewrite.

These seeds are the first rewrite-facing shape. They say that a local thunk is
forced under a known handler whose dynamic operation arm has a finite resume
schedule and whose reject arm does not resume. The optimizer still has not
rewritten code; the next destructive step should consume only `ReadyFinite`
seeds and either contify the thunk/body/handler region or leave the generic
runtime path untouched.

The current rewrite-plan view classifies all three 20x20 seeds as
`DefunctionalizeFiniteHandler`, not `CalleeBodyClone`:

```text
root_0 list(thunk entry 1):
  blockers: post_call_force_chain, callee_has_handlers, callee_has_effect_boundary
list__mono3 recursive list(thunk entry 8):
  blockers: recursive_callee, post_call_force_chain, callee_has_handlers, callee_has_effect_boundary
list__mono3 recursive list(thunk entry 9):
  blockers: recursive_callee, post_call_force_chain, callee_has_handlers, callee_has_effect_boundary
```

This keeps the inline intuition precise. The useful operation is to specialize
the finite handler/thunk/control region; ordinary callee body cloning crosses
the thunk surface and handler boundary without preserving the return-frame /
prompt protocol.

## First Destructive Rewrite Attempt

An experimental pass, gated behind `YULANG_CPS_ENABLE_READY_FINITE_INLINE=1`,
tries to consume a `ReadyFinite` seed by cloning the callee CPS body into the
caller and converting the direct-call return into a local continuation. This is
kept disabled by default.

The attempt exposed a real protocol boundary:

- A direct call result may be a thunk surface at the caller even when the cloned
  callee body computes the forced value internally.
- The caller's immediate `ForceThunk` chain must be consumed when the callee
  body is inlined; otherwise a list pointer is later treated as a thunk.
- Even after consuming that force chain, the generated native executable for
  the 20x20 benchmark still misroutes a scalar-like value into `list_merge`.

So plain function-body cloning is not a valid optimization yet. The rewrite
must preserve the CPS return-frame / prompt protocol and ABI lane expected by
the caller, or lower the whole handler/thunk region through a dedicated
defunctionalized representation instead of pretending the callee body is an
ordinary direct-style function body.
