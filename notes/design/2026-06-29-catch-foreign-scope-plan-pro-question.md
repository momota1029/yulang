## Verdict

**Yes: model `CatchForeign` as a scope-local handler/request boundary delta next.**
With 100% ScopePlan shadow coverage, `root_marker_mismatch = 0`, and all hot request lanes classified as `CatchForeign`, a `None | CatchSameHandler` executor would be structurally correct but practically cold.

But the important wording is:

```text
CatchForeign is a pass-through catch boundary delta,
not a handler match,
not a generic fallback,
not a provider-permission cert.
```

So I’d implement it as a **scope-local suspended boundary** with dual semantics:

```text
on request/signal: preserve boundary and continue outward
on value resume: run the catch value/normal-result behavior exactly like legacy CatchBody
```

That second half is the trap. `CatchForeign` is not only a request-lane thing. Legacy `resume_continuation` handles `CatchBody` on value resume by calling `continue_catch_body_result(...)` before continuing to `next`, so a direct executor that only models request pass-through is incomplete.

---

## 1. Invariant needed to execute `CatchForeign`

The needed invariant is:

```text
A CatchForeign boundary may be skipped for handler selection,
but it must be preserved as an ordered continuation boundary
with the same value-resume behavior, marker exposure, provider scope ordering,
and request fallback classification as the legacy tree.
```

More concretely:

```rust
struct CatchForeignBoundaryDelta {
    catch_expr: ExprId,
    arms: Rc<[CatchArm]>,
    env: Env,

    routed_handler: ExprId, // must differ from catch_expr
    position: ScopeBoundaryPosition,
    marker_baseline: MarkerDigest,
    provider_baseline: ProviderScopeDigest,
}
```

And the cert condition should be something like:

```text
- routed_handler is known
- catch_expr != routed_handler
- the boundary is transparent for current handler selection
- the boundary is not transparent for continuation semantics
- ProviderEnv child scope split preserves root marker
- marker/provider deltas before and after the boundary match legacy order
- materializing only this boundary delta plus the planned lanes gives the same normalized continuation shape as legacy
- one-shot only for the first executor
```

The distinction is subtle but crucial:

```text
transparent for dispatch ≠ removable from continuation
```

In the legacy direct-tail path, a foreign catch does not handle the call. It appends a `CatchBody` frame to the carried continuation and then continues with the outer `next`. That is exactly the shape your ScopePlan executor needs to preserve.

---

## 2. Is `CatchForeign` an outer boundary or generic fallback?

**It is an outer handler boundary that should be preserved. It does not force generic request fallback by itself.**

For a routed/direct-tail signal with target handler `H`, a `CatchBody` with `catch_expr != H` is not the matching handler. The runtime’s behavior is:

```text
foreign catch:
  do not handle here
  append/preserve this catch boundary into the request/continuation
  continue outward
```

The routed request path has the same structure: if the routed handler differs from `catch_expr`, the runtime appends the `CatchBody` frame to the request continuation and continues outward.

So `CatchForeign` should **not** be represented as:

```text
GenericFallback
Unhandled
Invisible
RequestBoundaryThatConsumesTheSignal
```

It should be represented as:

```text
PassThroughCatchBoundary {
    on_signal: push boundary delta onto carried continuation,
    on_value: execute CatchBody value semantics,
}
```

A generic request with no routed handler is different. That is `CatchNoRoutedHandler`, not `CatchForeign`. I would reject that from the first `CatchForeign` executor slice.

---

## 3. Can the first executable ScopePlan include `ProviderDirtyForeignCatchScope`?

**Yes, with one naming/meaning caveat.**
I would avoid making `ProviderDirtyForeignCatchScope` sound like a permission cert. It should certify **scope-local preservation**, not permission visibility.

Something like this is safer:

```rust
struct ForeignCatchScopeExecCert {
    routed_handler: ExprId,
    catch_expr: ExprId,

    // certifies exact pass-through catch behavior
    catch_delta: CatchBoundaryDeltaId,

    // certifies scope shape, not permission truth
    root_marker_digest: MarkerDigest,
    marker_delta: MarkerDeltaId,
    provider_child_scopes: Rc<[ProviderChildScopeId]>,

    // certifies that the produced continuation shape can be normalized
    // to the legacy shape
    continuation_shape_digest: ContinuationShapeDigest,

    multiplicity: OneShot,
}
```

Then if you want to keep the provider dirtiness in the name, split it:

```rust
struct ProviderDirtyScopeCert { ... }
struct ForeignCatchPassThroughCert { ... }

struct ProviderDirtyForeignCatchScopeCert {
    provider: ProviderDirtyScopeCert,
    catch: ForeignCatchPassThroughCert,
}
```

That makes it harder to accidentally use the catch cert as provider evidence.

The first executable subset can be:

```text
- one-shot only
- root marker match
- ProviderEnv child scopes
- CatchForeign request/boundary lane
- no RefSet boundary
- no CatchNoRouted
- no CatchSame handling inside this slice
- no legacy bridge
- no unrepresented resume_delta
- legacy materialize fallback available
```

The executor action for `CatchForeign` should be:

```text
DirectTail / RoutedYield:
  append CatchForeignBoundaryDelta to the carried continuation
  continue executing outer scope lanes

Value resume:
  run CatchBody value semantics from the delta
  then continue with outer scope
```

If your current lane model cannot express the value-resume half, do not enable direct execution yet. Add that representation first.

---

## 4. What to shadow-compare before enabling it?

Your proposed list is exactly right, but I’d make each item more concrete.

### A. Request / signal classification

Compare legacy vs planned:

```text
DirectTailResumptive stays DirectTailResumptive
RoutedYield stays RoutedYield
GenericRequest stays GenericRequest
DirectAbortive stays DirectAbortive
Unhandled stays Unhandled
```

A `CatchForeign` pass-through must not turn a routed/direct-tail signal into generic fallback.

### B. Routed handler and catch relation

Record:

```text
foreign_catch_routed_handler_known
foreign_catch_expr_ne_routed_handler
foreign_catch_expr_eq_routed_handler_reject
foreign_catch_no_routed_handler_reject
```

If `routed_handler` is absent, it is not this cert.

### C. Request visibility

Compare:

```text
legacy visible / planned visible
legacy handler target / planned handler target
legacy route cert / planned route cert
```

For `CatchForeign`, visibility should be preserved for the eventual matching handler. The foreign catch itself should not make the request visible or invisible.

### D. Handler boundary exposure

Compare a normalized digest of:

```text
guard_ids
carried_guards
handler_boundary
active handler frame exposure
```

Root marker match alone is not enough. It catches one class of scope bug, but not all handler exposure bugs.

### E. Provider grant gate

Compare:

```text
provider grant id
scope id
hygiene baseline
gate pass/fail
fail reason:
  no grant
  missing grant
  scope missing
  add-id shadowed
  handler shadowed
```

The catch cert must not change provider grant classification.

### F. Generic fallback classification

Compare:

```text
legacy fallback kind
planned fallback kind

direct-tail preserved?
routed yield preserved?
generic request preserved?
unhandled conversion identical?
```

Especially watch for accidental conversions around dirty provider grants.

### G. Produced continuation shape

This is the big one.

Do not compare raw tree pointers. Compare a normalized shape digest:

```text
Then ordering
CatchBody boundaries
MarkerFrame boundaries
ProviderEnv child scopes
RefSet boundaries
ordinary eval frames
scope entry/exit order
```

You want:

```text
materialize(scope_plan_delta) == normalize(legacy_continuation)
```

At least structurally. Full `Rc` identity does not matter; boundary order does.

### H. Value-resume behavior through the foreign catch

This needs its own shadow check:

```text
resume planned continuation with the same value
resume legacy continuation with the same value
compare result kind / root marker / next signal classification
```

This is where a request-only `CatchForeign` model would fail.

---

## 5. If `CatchForeign` cannot be executed directly, smallest representation change

The smallest change is **not** another flat trace and not full tree rebuild.

Add a boundary lane that is more general than request lane:

```rust
enum BoundaryLane {
    None,
    Catch(CatchBoundaryDeltaId),
    RefSet(RefSetBoundaryDeltaId),
}

enum CatchBoundaryMode {
    SameHandler,
    ForeignPassThrough,
    NoRoutedHandler,
}

struct CatchBoundaryDelta {
    catch_expr: ExprId,
    arms: Rc<[CatchArm]>,
    env: Env,
    mode: CatchBoundaryMode,
}
```

Then define dual behavior:

```rust
impl CatchBoundaryDelta {
    fn on_signal(&self, signal: Signal, cont: ScopeContinuation) -> Signal {
        match self.mode {
            CatchBoundaryMode::ForeignPassThrough => {
                signal.push_continuation_boundary(self.as_continuation_delta());
                signal
            }
            CatchBoundaryMode::SameHandler => {
                // handle, or reject in first slice
            }
            CatchBoundaryMode::NoRoutedHandler => {
                // generic request path, likely reject in first slice
            }
        }
    }

    fn on_value(&self, value: SharedValue) -> EvalResult {
        // equivalent to legacy continue_catch_body_result(...)
    }
}
```

That is the smallest representation that makes `CatchForeign` executable without rebuilding the whole legacy continuation tree.

If you only have:

```text
eval_lane
request_lane
marker_lane
```

then `CatchForeign` is awkward because it belongs to **request pass-through** and **value resume**. So I’d rename / generalize:

```text
request_lane -> boundary_lane
```

or split:

```text
request_lane: request/signal behavior
return_lane: value-resume behavior
```

I prefer `boundary_lane`, because `CatchBody` is one semantic boundary with two faces.

---

## First executable slice

I’d implement this exact slice:

```text
ScopePlan executor v1:

Accept:
  - one-shot
  - root marker match
  - ProviderEnv child scope split
  - BoundaryLane::Catch(ForeignPassThrough)
  - no RefSet
  - no CatchNoRouted
  - no same-handler handling
  - marker/provider deltas interned
  - legacy materialize fallback exists

Execute:
  - eval lane locally
  - marker lane locally
  - ProviderEnv child scopes locally
  - CatchForeign on signal: push boundary delta, continue outward
  - CatchForeign on value: run catch value semantics, continue outward

Reject:
  - missing routed handler
  - catch_expr == routed_handler
  - generic request requiring CatchNoRouted behavior
  - unrepresented provider/marker delta
  - continuation shape digest mismatch
```

This should hit the hot nondet/showcase lanes because the hot entries are exactly `CatchForeign`.

---

## Stop criteria

Do not enable if any of these are nonzero in shadow:

```text
foreign_catch_root_marker_mismatch
foreign_catch_materialize_shape_mismatch
foreign_catch_signal_kind_mismatch
foreign_catch_visibility_mismatch
foreign_catch_handler_boundary_mismatch
foreign_catch_provider_gate_mismatch
foreign_catch_fallback_class_mismatch
foreign_catch_value_resume_mismatch
```

Rollback if enabling gives:

```text
compare-control mismatch
adversarial hygiene mismatch
direct-tail → generic fallback increase
routed-yield → generic fallback increase
ProviderEnv miss treated as invisibility
any ProviderEnv treated as permission evidence
```

Performance counters to check after enabling:

```text
scope_exec_hits
scope_exec_foreign_catch_hits
scope_exec_tree_fallbacks

continuation_resume_steps
continuation_resume_then_steps
continuation_resume_catch_steps
continuation_resume_marker_steps
continuation_resume_provider_steps

catch_body_checks
catch_boundary_generic_request_signals
catch_boundary_direct_tail_signals

marker_frame_entries
active_add_id_scans
function_call_marker_plans
```

The expected first win is not “catch counter disappears”. The desired shape is:

```text
foreign catch pass-through no longer forces recursive tree decomposition,
while value-resume catch semantics remain identical.
```

---

## Final answer

**Yes, execute `CatchForeign` directly next, but only as a scope-local pass-through catch boundary with value-resume semantics.**

It does **not** force generic fallback. It is the foreign outer catch that legacy preserves in the carried continuation while continuing outward. The first ScopePlan executor can include a `ProviderDirtyForeignCatchScope`-style cert, but that cert must mean:

```text
scope/order preservation + foreign catch pass-through
```

not:

```text
provider permission proof
```

If your current request lane cannot model the value side of `CatchBody`, make the smallest representation change now: replace `request_lane` with a `boundary_lane` / `CatchBoundaryDelta` that has both `on_signal` and `on_value` behavior. That is the cleanest path to a narrow executor that actually hits the current hot workloads.

---

## Implementation note: CatchForeign boundary lane shadow

The first profile-only shadow has been implemented after this review. It does not execute the
ScopePlan yet. It checks whether the existing `EvidenceRequestDeltaPlan` can be treated as a
foreign catch boundary lane with both faces:

```text
signal side:
  foreign catch is transparent for handler selection

value side:
  catch arms/env are available for legacy CatchBody value-resume behavior
```

Deep profile:

```text
nondet:
  scope_plan_foreign_catch_candidates: 420
  scope_plan_foreign_catch_ready: 420
  scope_plan_foreign_catch_boundaries: 840
  scope_plan_foreign_catch_signal_passthrough_boundaries: 840
  scope_plan_foreign_catch_value_resume_boundaries: 840
  scope_plan_foreign_catch_legacy_materialize_fallback_available: 420
  rejects: all 0

showcase:
  scope_plan_foreign_catch_candidates: 829
  scope_plan_foreign_catch_ready: 829
  scope_plan_foreign_catch_boundaries: 1644
  scope_plan_foreign_catch_signal_passthrough_boundaries: 1644
  scope_plan_foreign_catch_value_resume_boundaries: 1644
  scope_plan_foreign_catch_legacy_materialize_fallback_available: 829
  rejects: all 0
```

Normal release keeps the sidecar disabled:

```text
scope_plan_foreign_catch_candidates: 0
compare.control: match
```

Reading:

- The hot `CatchForeign` lane is fully representable as a boundary lane in the representative
  workloads.
- This still is not an executor. The next slice should name the boundary delta explicitly and add
  shadow comparisons for:

```text
signal kind preservation
generic fallback classification
continuation shape digest after materialization
value-resume behavior through the foreign catch
```

Only after those are mismatch-free should the narrow executor use the boundary lane.

## Implementation note: first-class CatchForeign boundary delta surface

The next profile-only slice has named the boundary lane explicitly:

```text
EvidenceCatchBoundaryDeltaPlan
EvidenceCatchBoundaryMode::{SameHandler, ForeignPassThrough, NoRoutedHandler}
EvidenceCatchBoundaryShapeDigest
```

`EvidenceRequestDeltaPlan` still remains the source of truth, but it can now project a list of
catch boundary deltas and a mode digest. This keeps the current runtime behavior unchanged while
making the future executor target explicit.

Deep profile:

```text
nondet:
  scope_plan_catch_boundary_delta_plans: 420
  scope_plan_catch_boundary_delta_boundaries: 840
  scope_plan_catch_boundary_delta_foreign_pass_through: 840
  scope_plan_catch_boundary_delta_same_handler: 0
  scope_plan_catch_boundary_delta_no_routed: 0
  scope_plan_catch_foreign_boundary_delta_ready: 420
  scope_plan_catch_foreign_boundary_delta_signal_ready: 840
  scope_plan_catch_foreign_boundary_delta_value_resume_ready: 840
  scope_plan_catch_foreign_boundary_delta_shape_digest_ready: 420

showcase:
  scope_plan_catch_boundary_delta_plans: 829
  scope_plan_catch_boundary_delta_boundaries: 1644
  scope_plan_catch_boundary_delta_foreign_pass_through: 1644
  scope_plan_catch_boundary_delta_same_handler: 0
  scope_plan_catch_boundary_delta_no_routed: 0
  scope_plan_catch_foreign_boundary_delta_ready: 829
  scope_plan_catch_foreign_boundary_delta_signal_ready: 1644
  scope_plan_catch_foreign_boundary_delta_value_resume_ready: 1644
  scope_plan_catch_foreign_boundary_delta_shape_digest_ready: 829
```

Normal release still keeps the sidecar disabled:

```text
scope_plan_catch_boundary_delta_plans: 0
compare.control: match
```

Reading:

- The representative hot lanes remain entirely `ForeignPassThrough` after projection to the
  first-class delta surface.
- Signal and value sides are still only "ready" counters. The executor is not using these deltas.
- The next safe slice is an actual shadow comparison for signal kind preservation, generic fallback
  classification, continuation shape digest after legacy materialization, and value-resume behavior.

## Implementation note: CatchForeign boundary delta shadow comparison

The next profile-only slice compares the first-class delta projection against the legacy request
lane classification. It still does not execute the boundary lane.

Compared facets:

```text
signal kind preservation
generic fallback classification
materialized catch-frame shape digest
value-resume payload
```

Deep profile:

```text
nondet:
  signal_shadow: 840
  signal_match: 840
  signal_mismatch: 0
  generic_fallback_shadow: 840
  generic_fallback_match: 840
  generic_fallback_mismatch: 0
  materialized_shape_shadow: 420
  materialized_shape_match: 420
  materialized_shape_mismatch: 0
  value_resume_shadow: 840
  value_resume_match: 840
  value_resume_mismatch: 0

showcase:
  signal_shadow: 1644
  signal_match: 1644
  signal_mismatch: 0
  generic_fallback_shadow: 1644
  generic_fallback_match: 1644
  generic_fallback_mismatch: 0
  materialized_shape_shadow: 829
  materialized_shape_match: 829
  materialized_shape_mismatch: 0
  value_resume_shadow: 1644
  value_resume_match: 1644
  value_resume_mismatch: 0
```

Normal release still keeps these counters at 0 because the sidecar is disabled. Representative
normal runs stayed compare-control clean (`nondet` around 8.7ms, `showcase` around 19.7ms in this
run).

Reading:

- The `CatchForeignBoundaryDelta` projection is now structurally aligned with the legacy request
  lane for the representative hot paths.
- This is still not a semantic executor. It proves the target surface is coherent enough to try a
  narrow executor under a legacy fallback/shadow comparison.

## Implementation note: direct-tail CatchForeign delta append

A first runtime slice now routes direct-tail foreign catch materialization through a named
`CatchForeignBoundaryDelta` helper. It still materializes a normal `CatchBody` continuation for the
value-resume side, so this is not yet the full segment executor.

The useful change is narrower:

```text
normal release:
  skip the diagnostic provider-pair append probe for this foreign-catch direct-tail path

debug / deep-profile:
  keep the probe enabled
```

Normal profile:

```text
nondet:
  catch_foreign_boundary_delta_direct_tail_appends: 840
  catch_foreign_boundary_delta_direct_tail_scope_blockers: 420
  catch_foreign_boundary_delta_direct_tail_probe_enabled: 0
  catch_foreign_boundary_delta_direct_tail_probe_skipped: 420
  runtime_evidence_execute: 8.4ms - 9.4ms in the sampled runs

showcase:
  catch_foreign_boundary_delta_direct_tail_appends: 1644
  catch_foreign_boundary_delta_direct_tail_scope_blockers: 822
  catch_foreign_boundary_delta_direct_tail_probe_enabled: 0
  catch_foreign_boundary_delta_direct_tail_probe_skipped: 822
  runtime_evidence_execute: 20.5ms - 21.0ms in the sampled runs
```

Deep profile keeps the old probe visible. For `nondet`, the probe reports `provider_pair: 420` and
`reject_handler_path: 420`, with compare-control still matching.

Reading:

- This is a small runtime cleanup, not the full `CatchBoundarySegment` executor.
- The remaining large boundary is still the scope-preserving `Then` / value-resume `CatchBody`
  materialization.
- A larger executor should keep the same invariant: signal side passes through the foreign catch,
  value side retains full `CatchBody` behavior.
