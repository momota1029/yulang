# Evidence VM hierarchical ResumePlan sketch

## Context

The current ResumePlan sidecar has three useful pieces:

- payload lanes: `EvalDelta`, `RequestDelta`, `MarkerDelta`, `ProviderDelta`
- accepted certs for `ProviderDirtyForeignCatchScope`
- an ordered flat trace over `Eval` / `Request` / `Marker` / `Provider` steps

The flat trace is not executable yet. Deep profile shows:

```text
nondet:
  resume_plan_exec_shadow_checks: 420
  resume_plan_exec_shadow_ready: 0
  resume_plan_exec_shadow_reject_trace_marker_bounds: 420

showcase:
  resume_plan_exec_shadow_checks: 822
  resume_plan_exec_shadow_ready: 0
  resume_plan_exec_shadow_reject_trace_marker_bounds: 822
```

The important reading is that a single flat trace over all continuation frames does not match the
current lane ownership rules. In particular, `ProviderEnv` is a scope boundary. A marker frame that
appears under a provider scope is not simply another top-level marker-lane frame.

So the next executor must not consume `trace + flat lanes` directly.

## Principle

Do not flatten provider scope to make the trace pass.

The semantic shape should be:

```text
Root resume scope
  ordinary eval / request / marker steps
  provider enter step
    child provider scope
      ordinary eval / request / marker steps
      nested provider enter step
```

That is, `ProviderEnv` should own a child resume scope. The executor enters the provider scope,
executes that child trace with the provider environment active, and then returns to the parent trace.

This preserves the existing boundary rule:

```text
ProviderEnv is not an ordinary continuation frame,
but it is also not erased.
```

It becomes a scoped plan segment.

## Possible representation

One compact direction is to make scope explicit:

```rust
struct EvidenceResumePlan {
    root: EvidenceResumeScopeId,
    scopes: Rc<[EvidenceResumeScopePlan]>,
}

struct EvidenceResumeScopePlan {
    steps: Rc<[EvidenceResumeScopedStep]>,
    eval: EvidenceEvalDeltaId,
    request: EvidenceRequestDeltaId,
    marker: EvidenceMarkerDeltaId,
}

enum EvidenceResumeScopedStep {
    Eval(usize),
    Request(usize),
    Marker(usize),
    Provider(EvidenceProviderDeltaId, EvidenceResumeScopeId),
}
```

Another direction is to keep global lanes but tag each step with a scope id:

```rust
struct EvidenceResumePlanStep {
    scope: EvidenceResumeScopeId,
    kind: EvidenceResumePlanStepKind,
}
```

The first representation is cleaner for execution. The second representation is easier as a
transition from the current flat trace. Either way, the important point is that provider-contained
marker frames must not be forced into the root marker lane.

## Next safe patch

The next implementation should still avoid execution changes.

1. Build a scope-aware trace shadow.
2. Count how many marker/request/eval steps live in root scope vs provider child scope.
3. Validate that each scope consumes its own lane payload exactly once.
4. Keep normal release at zero sidecar work.

Suggested counters:

```text
resume_plan_scoped_trace_plans
resume_plan_scoped_trace_scopes
resume_plan_scoped_trace_provider_child_scopes
resume_plan_scoped_trace_root_steps
resume_plan_scoped_trace_child_steps
resume_plan_scoped_trace_ready
resume_plan_scoped_trace_reject_eval_bounds
resume_plan_scoped_trace_reject_request_bounds
resume_plan_scoped_trace_reject_marker_bounds
resume_plan_scoped_trace_reject_unused_payload
```

Success condition:

```text
deep profile:
  scoped_trace_ready > 0
  scoped_trace_reject_marker_bounds drops from all accepted plans
  compare.control: match

normal release:
  scoped_trace_plans: 0
```

Only after this passes should a narrow executor be attempted.

## First executable slice

The first execution slice should be narrower than the representation:

```text
- DirectTailResumptive only
- ProviderDirtyForeignCatchScope cert only
- one-shot only
- no RefSet boundary
- no legacy bridge
- no resume-delta unless represented in the scope plan
- fallback can materialize the old tree
```

The executor should be allowed to bail out at any unsupported scoped step. The fallback must keep
the old tree intact.

## Why not native or bytecode yet

Native compilation or bytecode before this split would compile the current tree-walking shape. The
main cost is still the runtime representation of resume scope, not instruction dispatch alone.

The useful intermediate IR is therefore:

```text
CatchBody / MarkerFrame / ProviderEnv outside the ordinary continuation spine,
with scope boundaries represented explicitly.
```

Once this exists, bytecode or native can target it.
