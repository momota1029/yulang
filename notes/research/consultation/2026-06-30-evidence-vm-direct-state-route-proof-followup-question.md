# ChatGPT Pro consultation follow-up: Evidence VM direct state route proof

Paste the answer here:

- `notes/research/consultation/2026-06-30-evidence-vm-direct-state-route-proof-followup-answer.md`

## Question

Please answer in Japanese.

I asked for a concrete implementation proof for route-specific
`DirectStateGet/Set` in:

- `notes/research/consultation/2026-06-30-evidence-vm-direct-state-route-proof-question.md`

The answer was pushed into a different file:

- `notes/research/consultation/2026-06-30-local-ref-loop-runtime-answer.md`

That answer is useful, but I need one clarification before continuing. It says:

```text
compiler certificate
  -> KnownHandlerPlan::State
  -> RuntimeStateHandlerFrame
  -> late direct get/set at catch boundary
  -> snapshot/fork canaries

Then move to:

DirectStateGet/Set at operation call site
  -> StateRef direct RefSet assignment
```

It also says route-specific `DirectStateGet/Set` requires:

```text
operation call route proves handler H is visible
H has KnownHandlerPlan::State P
operation is P.get or P.set
route is not blocked/delayed/callback-unsafe
```

Current Yulang state:

- Stage A plan-only known operation classification exists.
- Stage B `RuntimeStateHandlerFrame` storage exists.
- Late catch-boundary known-state direct get/set exists.
- A first nondet canary exists.
- Representative `bench/loop_for_sum_ref_20_discard.yu` is already much better:
  - release `debug evidence-vm-run --compare-control`: match
  - release runtime evidence execute: about `66ms`
  - `known_state_direct_gets: 800`
  - `known_state_direct_sets: 400`
  - `known_operation_state_get_active_frame_hits: 800`
  - `known_operation_state_set_active_frame_hits: 400`
- But static call-site route proof is still absent:
  - operation execution: `generic-fallback`
  - operation visibility: `legacy_bridge=true`
  - known operation reject: `no-candidate-handler`
  - `direct_effect_calls: 0`

## Clarification needed

Was the previous answer intended to mean:

```text
Do not implement route-specific DirectStateGet/Set yet.
Implement explicit continuation snapshot/fork for runtime state frames first.
Then return to route proof.
```

If yes, please give a concrete implementation plan for Stage C in the current
Evidence VM architecture.

If no, please give the missing direct route proof for Stage D.

## Current architecture detail relevant to Stage C

Runtime state frames are currently outside continuations:

```rust
struct RuntimeStateHandlerFrame {
    catch_expr: ExprId,
    plan_id: EvidenceVmKnownHandlerPlanId,
    state_def: DefId,
    state: SharedValue,
}

struct RuntimeEvidenceRunner {
    active_state_handler_frames: Vec<RuntimeStateHandlerFrame>,
    ...
}
```

Entering a known-state catch pushes a frame:

```text
eval_catch:
  push_known_state_frame_for_catch(catch_expr, env)
  eval body
  pop_known_state_frames(old_len)
```

Continuations are represented only by `EvidenceContinuation` frames. They do
not currently carry `RuntimeStateHandlerFrame` snapshots.

When an unhandled request crosses a catch boundary:

```rust
fn defer_catch_body(
    &mut self,
    catch_expr: ExprId,
    arms: Rc<[control_vm::CatchArm]>,
    env: &Env,
    request: EvidenceRequest,
) -> EvidenceRequest {
    let env = self.clone_env(env);
    self.append_request_continuation(
        request,
        EvidenceContinuation::catch_body(
            catch_expr,
            arms,
            env,
            EvidenceContinuation::identity(),
        ),
    )
}
```

This appends catch-body continuation state, but not active known-state frames.

## Important semantic distinction

Please be precise about handler ordering.

Case 1: state handler outside nondet/list handler.

```yulang
use std::control::nondet::*

{
  my $x = 0
  my ys = {
    my b = each [true, false]
    &x = $x + 1
    $x
  }.list
  (ys, $x)
}
```

Current and control behavior:

```text
run roots [([1, 2], 2)]
```

This should remain shared state across nondet branches.

Case 2: state handler inside a continuation captured by an outer multi-shot
handler.

Conceptually, this should fork/snapshot state per resumed continuation branch:

```text
outer multi-shot handler resumes k twice
state handler is inside k
first resume mutates local state
second resume should start from the captured state, not from the first resume's mutation
```

I need the exact runtime rule that distinguishes these two cases in this
Evidence VM structure.

## Concrete questions

1. Where should `RuntimeStateHandlerFrame` snapshots be stored?
   - A new `EvidenceContinuationFrame::StateFrames { ... }`?
   - Inside `CatchBody`?
   - Inside `EvidenceRequest`?
   - Somewhere else?

2. Where should the snapshot be created?
   - When a request is created?
   - In `defer_catch_body` when a request crosses a known-state catch?
   - In `append_request_continuation`?
   - Somewhere tied to the handler that actually captures the continuation?

3. If `defer_catch_body` is the right place, should it:
   - wrap the existing request continuation so state is active while the original
     continuation resumes, or
   - append a state frame after the original continuation?

   My current concern is that appending after the original continuation is too
   late for direct state get/set during the resumed continuation.

4. How should nested known-state handlers be ordered in the snapshot?

5. On resume, should snapshot frames:
   - push onto `active_state_handler_frames` for the duration of the resumed
     continuation,
   - update the env-shadow slot too,
   - increment existing frame entry/exit counters,
   - increment separate `known_state_frame_snapshots` / `known_state_frame_forks`
     counters?

6. How do we avoid breaking the shared-state case where state is outside a
   nondet/list handler?

7. What minimal canary should be added before any Stage D request-free direct
   state execution?

8. Once Stage C is in place, is active state frame hit plus `KnownOperationPlan`
   still insufficient for Stage D if the operation object remains
   `generic-fallback` / `legacy_bridge=true` / `no-candidate-handler`?

9. If it is still insufficient, what exact proof object should be added to move
   local-ref known operations from `no-candidate-handler` to direct-ready without
   source-name/path matching?

## Constraints

- Do not suggest a raw `Rc<RefCell<Value>>` local cell.
- Do not rely on benchmark names, file paths, source variable names, or std path
  string matching as runtime proof.
- Do not weaken marker/provider hygiene.
- Do not make arbitrary user refs, file refs, or projected refs direct unless
  separately certified.
- Preserve payload evaluation order.
- Preserve the shared-state behavior of state outside nondet/list handlers.
