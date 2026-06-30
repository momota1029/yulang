# Known State Handler Plan

## Goal

`for` plus local mutable refs is currently catastrophic because a simple state
update goes through generic effect machinery:

```text
record select -> update_effect -> ref_update -> get -> set -> catch/resume
```

The fix should not make local variables a one-off runtime special case. The
optimization target is a certified known state handler:

```text
KnownHandlerPlan::State
  -> RuntimeStateHandlerFrame
  -> direct StateGet / StateSet
```

The first producer may be compiler-generated local mutable var lowering, but the
runtime mechanism is a known-handler plan, not `my $x` hard-coding.

## Current Baseline

Warm release `run.runtime_execute` measurements from 2026-06-30:

- recursive sum loop: `1.4ms` to `1.6ms`
- `for` without mutable ref: about `6ms`
- `for` with `my $total` and `&total = ...`: about `1.8s` to `2.0s`
- nondet `(each 1..20 + each 1..20).list`: about `10ms`

Reading:

- Pure recursion is not the problem.
- `for` is slower than recursive loops, but not the 2-second problem.
- The catastrophic path is local state implemented through generic effects.

## Design Split

Type/evidence route and state-handler certification are separate facts.

```text
type/control evidence:
  proves an operation call reaches a handler/capability

state handler certificate:
  proves that handler implements the get/set state algebra

runtime state frame:
  stores certified handler state and participates in continuation snapshot/fork
```

Type/evidence alone cannot prove handler meaning. A handler with the same row and
types may ignore `set`, log on `get`, resume twice, forward operations, or let the
continuation escape. A state fast path is valid only when both routing and a
state-handler certificate hold.

## First Certified Shape

Stage 1 only accepts compiler-generated local var handlers with the state algebra:

```text
run(state, body) =
  catch body:
    get(), k     -> run(state, k(state))
    set(new), k  -> run(new, k(()))
```

The checker should accept only the narrow form needed for local mutable refs:

- one state parameter and one computation parameter
- exactly one hygienic effect family with `get` and `set`
- no arm guards
- continuation binder exists
- continuation is used exactly once
- continuation does not escape
- no delayed/callback boundary around the continuation use
- arm body re-enters the same handler with the selected next state

User handler shape recognition is explicitly later work. The first producer is a
compiler-generated certificate, not arbitrary source-shape matching.

## Runtime Shape

The planned surface:

```rust
enum KnownHandlerPlan {
    State(StateHandlerPlan),
}

struct StateHandlerPlan {
    plan_id: KnownHandlerPlanId,
    handler_expr: ExprId,
    family: EffectFamilyId,
    get_op: OperationId,
    set_op: OperationId,
    source: StateHandlerSource,
    continuation_semantics: StateContinuationSemantics,
}

enum StateHandlerSource {
    CompilerCertificate(SyntheticLocalVarId),
    ShapeCheckedAnnotation(AnnotationId), // later
}

enum StateContinuationSemantics {
    SnapshotFork,
}
```

Execution should eventually expose route-specific plans:

```rust
enum EvidenceVmOperationExecutionPlan {
    DirectStateGet { state_plan: KnownHandlerPlanId },
    DirectStateSet { state_plan: KnownHandlerPlanId },
    // existing direct/generic variants...
}
```

The direct operation must touch an active state handler frame selected by
capability/allowed-set/plan identity, not by a raw source name or record field
shape.

## Escaped Refs

`std.control.var.ref` remains the public abstraction. Internally, escaped refs
may later use a tagged runtime representation:

```rust
enum RefRepr {
    StateSlot(StateRef),
    Generic(Value),
    Projection(ProjectionRef), // later
}
```

First direct execution does not need generic receiver fast paths. It can start
with only:

- `$x` -> `StateGet`
- `&x = value` -> `StateSet`

`r.get()`, `r.update(f)`, file refs, user refs, and projected refs remain on the
generic protocol until later stages.

If a `StateRef` escapes outside the dynamic state-handler extent, it must not
turn into a persistent heap cell. It should match the current generic semantics:
fallback or unhandled effect/runtime error, according to the existing behavior.

## Continuation Semantics

State in a `RuntimeStateHandlerFrame` is part of the dynamic continuation, just
like the `state` argument in the current handler recursion. Captured
continuations therefore use snapshot/fork semantics.

```text
capture at x = 10
resume k ()  -> branch A starts with x = 10
resume k ()  -> branch B starts with x = 10
branch A writes x = 20
branch B still starts from x = 10
```

One-shot destructive reuse is only an optimization after one-shot use is proven.
Raw shared cells are not the default semantics.

## `ref_update` And Projection

`ref_update` remains the generic focused-update protocol.

Stage 1 only targets direct local get/set. `r.update(f)` is later because it must
preserve this order:

```text
old = read state slot
new = evaluate f(old) in the same dynamic context
write state slot only after f returns normally
```

Projection direct updates are a later `ProjectionPlan` / lens-chain optimization.
Until then, projected refs use the existing `update_effect` / `ref_update`
protocol.

## Stages

Current implementation status on 2026-06-30:

- Stage 0 generic ref-set counters are present in runtime stats and CLI output.
- Stage 1 plan/object surface is present:
  - `EvidenceVmKnownHandlerPlan::State`
  - `EvidenceVmObjectPlan::known_handlers`
  - known-handler summary/debug counters
- Stage 1 compiler-local-var producer is present:
  - lowering records `poly::expr::SyntheticVarEffect`
  - specialize carries it in `RuntimeEvidenceSurface::known_state_handlers`
  - evidence-vm pairs certified families with same-handler `get` / `set` arms
- Stage 2 first execution slice is present:
  - `EvidenceVmKnownStateHandlerPlan` records the compiler-generated `run`
    state parameter.
  - runtime context builds a catch-indexed known-state lookup.
  - after the existing operation visibility check succeeds, `get` resumes the
    operation continuation with the current runtime state frame value and
    `set` writes the runtime state frame before resuming with unit.
  - `set` still also shadows the old env state slot as a compatibility path for
    generic fallback code.
  - `RefSet` still uses the generic `update_effect` / `ref_update` path.
  - route-specific `DirectStateGet/Set` operation execution is still later work.
- Stage A follow-up plan-only `KnownOperationCall` classification is present:
  - `EvidenceVmObjectPlan::known_operations` records certified state `get` /
    `set` call sites that intersect a `KnownHandlerPlan::State`.
  - plan/debug counters distinguish static call-site candidates from runtime
    candidate hits.
  - current compiler-local refs classify as state get/set candidates but reject
    route-specific direct execution with `no-candidate-handler`; operation
    objects still execute through `generic-fallback`.
- Stage B semantic storage migration is present for the late intercept:
  - known state catch entry pushes a runtime state handler frame.
  - late catch-boundary known-state `get` / `set` reads and writes that frame.
  - counters report frame entry/exit, late reads/writes, frame misses, and env
    shadow compatibility fallbacks.

### Stage 0: Plan Surface, Counters, Canaries

No behavior change.

- Add design and debug surfaces for known state plans.
- Add counters for state-plan candidates/fallbacks and current generic ref path.
- Add semantic canaries comparing generic behavior before enabling direct state.
- Keep the feature gate off.

### Stage 1: Plan-Only Known State Handler

Produce `KnownHandlerPlan::State` for compiler-generated local mutable vars, but
do not execute it. Print/debug the plan and fallback reasons.

Rollback: ignore the plan.

### Stage 2: Direct Local Read/Write

Use direct execution only for compiler-known local state requests after the
existing catch visibility check proves the operation is visible to the certified
handler. The first slice intercepts generic catch requests. Route-specific
`DirectStateGet/Set` plans remain later work.

Rollback: disable the known-state catch intercept and fall back to
`eval_operation_arm`.

### Stage B Follow-Up: Runtime State Handler Frame

The late catch-boundary intercept uses runtime state handler frames as semantic
storage.

- Push a state frame when entering a certified known-state catch.
- Keep it active until the catch body and handler continuation processing finish.
- Read/write the frame in the existing late known-state intercept.
- Keep env shadow writes as compatibility for fallback code until route-specific
  direct state ops and continuation snapshot/fork canaries are in place.

Rollback: ignore the active state frame and read/write the env shadow path.

### Stage A Follow-Up: Plan-Only Known Operation Calls

No behavior change.

- Join known state handler certificates with concrete operation call sites.
- Print `known-operation-calls` and plan counters for state get/set candidates,
  direct-ready candidates, and reject reasons.
- Count runtime candidate hits from forced effect thunks so hot benchmarks can
  compare static call sites with dynamic request volume.

Rollback: ignore `EvidenceVmObjectPlan::known_operations`.

### Stage 3: Snapshot/Fork

Capture active state handler frames in continuation snapshots and fork them on
multi-shot resume. Do not default-enable direct state before canaries pass.

Current canary status:

- A known state frame active across a nondet resume path matches the control VM
  on `([1, 2], 2)` and does not lose the active frame.
- Full state-frame snapshot/fork representation is still later work before
  route-specific `DirectStateGet/Set` is enabled.

### Stage 4: Escaped `StateRef` Receiver Fast Path

Allow `&x` passed to generic code to remain fast when the matching active frame is
available. Otherwise preserve current fallback/error behavior.

### Stage 5: `r.update(f)` Fast Path

Add only after evaluation-order and continuation canaries are in place.

### Stage 6: Structural Projection Plans

Add record/tuple/list lens plans separately. Do not fold projection into the
first state-handler change.

### Stage 7: Checked User State Handlers

Introduce an explicit annotation/certificate producer for user handlers and run
the same state-handler checker.

## Canaries

Basic state:

- single local var read/write
- shadowed vars
- two independent locals updated interleaved
- nested handlers with same operation names but different hygienic identities

Generic ref boundary:

- `&x` passed to a function that calls `r.get()`
- `&x` passed to a function that calls `r.update(f)`
- `&x` stored in record/tuple/list and used inside scope
- `&x` returned outside scope matches current generic behavior
- user/file refs remain generic

Continuation/multi-shot:

- capture after update, resume twice, both branches start from captured state
- nondet around local state update matches generic VM
- escaped state ref inside captured closure remaps to the resumed frame

Hygiene:

- blocked route never performs direct state get/set
- delayed/callback boundary falls back unless explicit evidence carries provider
- same operation name in different hygienic families does not collide

`ref_update` order:

- `r.update(f)` observes old state
- write happens only after `f` returns normally
- generic projection keeps current focused-update behavior

## Avoid

- matching std paths or source names
- matching records with `get` / `update_effect` fields
- arbitrary handler source-shape equivalence
- raw shared `Rc<RefCell<Value>>` semantics
- enabling direct state before snapshot/fork canaries
- treating `ref_update` as only local assignment
- direct access across blocked/delayed routes
- `Any` as a fallback for unknown handler shapes
- downstream output patching
