# ChatGPT Pro consultation: Evidence VM direct state route proof

Paste the answer here:

- `notes/research/consultation/2026-06-30-evidence-vm-direct-state-route-proof-answer.md`

## Question

Please answer in Japanese.

I am working on Yulang, a language with algebraic effects, effect rows,
handlers, marker/provider hygiene, and an interpreter called Evidence VM.

The previous consultation recommended the following staged direction:

```text
A. plan-only KnownOperationCall classification
B. RuntimeStateHandlerFrame storage
C. snapshot/fork canaries
D. route-specific DirectStateGet/Set request-free call sites
E. certified RefSet direct assignment
```

I implemented A, B, a first C canary, and an extra observation counter for the
precondition of D. I deliberately did not implement route-specific
`DirectStateGet/Set`, because the implementation proof for D still seems
incomplete.

I need a concrete implementation proof for D, or a correction if D is still not
safe.

## Current committed state

Recent commits:

- `41ca4475 Add plan-only known operation classification`
- `2ebc7403 Move known state intercept to runtime frames`
- `ef1ce9da Add known state frame nondet canary`
- `2b57c680 Track known operation active state frames`

Relevant design note:

- `notes/design/2026-06-30-known-state-handler-plan.md`

Relevant previous answer:

- `notes/research/consultation/2026-06-30-evidence-vm-general-handler-speedup-answer.md`

## What is now implemented

### Known state handler plan

Evidence VM has:

- `EvidenceVmKnownHandlerPlan::State`
- compiler-local-var certificates from lowering/specialize
- `EvidenceVmKnownStateHandlerPlan`
  - `id`
  - `handler`
  - `state`
  - `family`
  - `get_handler_id`
  - `set_handler_id`
  - `source`
  - `continuation`

This is still certificate-based. User-written state-like handlers do not become
known handlers without the compiler certificate.

### Plan-only known operation classification

Evidence VM now has:

- `EvidenceVmObjectPlan::known_operations`
- `EvidenceVmKnownOperationPlan`
  - `expr`
  - `apply`
  - `callee`
  - `known_handler`
  - `handler_id`
  - `role: StateGet | StateSet`
  - `direct_ready`
  - `reject`
  - `visibility`

For `bench/loop_for_sum_ref_20_discard.yu`:

```text
known_operation_calls: 3
state_get_candidates: 2
state_set_candidates: 1
direct_gets: 0
direct_sets: 0

known-operation-calls:
  state-get reject no-candidate-handler
  state-get reject no-candidate-handler
  state-set reject no-candidate-handler
```

Important: static plan candidates are 2 get call sites and 1 set call site.
Dynamic hits are 800 gets and 400 sets.

### Runtime state frame storage

The existing late catch-boundary direct known-state intercept now uses runtime
state frames:

- entering a certified known-state catch pushes `RuntimeStateHandlerFrame`
- late known-state `get` reads the frame
- late known-state `set` writes the frame
- `set` still also writes the old env-shadow state slot as compatibility
- env-shadow fallback counters exist and are currently 0 in representative
  local-ref cases

### Current counters

Plan counters include:

```text
plan_known_operation_calls
plan_known_operation_state_get_candidates
plan_known_operation_state_set_candidates
plan_known_operation_state_direct_gets
plan_known_operation_state_direct_sets
plan_known_operation_reject_*
```

Runtime counters include:

```text
known_state_direct_gets
known_state_direct_sets
known_state_frame_entries
known_state_frame_exits
known_state_frame_reads_late
known_state_frame_writes_late
known_state_frame_missing_late
known_state_frame_shadow_compat_fallbacks

known_operation_state_get_candidate_hits
known_operation_state_set_candidate_hits
known_operation_state_get_active_frame_hits
known_operation_state_set_active_frame_hits
known_operation_state_get_active_frame_misses
known_operation_state_set_active_frame_misses
known_operation_state_direct_get_plan_hits
known_operation_state_direct_set_plan_hits
```

## Current representative measurements

Release run:

```sh
target/release/yulang run --runtime-phase-timings --print-roots \
  bench/loop_for_sum_ref_20_discard.yu
```

Representative output:

```text
run.runtime_execute: 51.8ms

known_state_direct_gets: 800
known_state_direct_sets: 400

known_state_frame_reads_late: 800
known_state_frame_writes_late: 400
known_state_frame_missing_late: 0
known_state_frame_shadow_compat_fallbacks: 0

known_operation_state_get_candidate_hits: 800
known_operation_state_set_candidate_hits: 400
known_operation_state_get_active_frame_hits: 800
known_operation_state_set_active_frame_hits: 400
known_operation_state_get_active_frame_misses: 0
known_operation_state_set_active_frame_misses: 0
```

Debug compare-control:

```text
target/release/yulang debug evidence-vm-run --compare-control \
  bench/loop_for_sum_ref_20_discard.yu

compare.control: match
```

## The exact blocker

The runtime facts are now promising:

```text
known operation candidate is forced
matching runtime state frame is active
dynamic hit count is exactly 800/400
```

But the plan facts are still not sufficient:

```text
operation object execution: generic-fallback
known operation reject: no-candidate-handler
direct_effect_calls: 0
```

So the missing proof is:

> How do we safely prove, at the operation call site, that this certified known
> operation reaches this known state handler under marker/provider/hygiene
> semantics, before allocating a generic effect request?

I do not want to turn this into:

- source-name/path matching
- compiler-local-var-only VM cells
- a shortcut that only checks whether an active state frame happens to exist
- a shape-based recognition of arbitrary user handlers
- a weakening of marker/provider hygiene

## What I need from you

Please give a concrete implementation proof for route-specific
`DirectStateGet/Set`.

The answer should be specific enough that an implementation can follow it
without guessing. Please include exact data structures, where they are built,
runtime guards, fallback behavior, and counters.

## Specific questions

1. Is `active state frame hit == 800/400` a sufficient runtime precondition for
   direct state execution?
   - If not, what static/dynamic proof is still missing?

2. The current `KnownOperationPlan` has `known_handler`, `handler_id`, `role`,
   and `visibility`, but rejects direct readiness with `no-candidate-handler`.
   What should be added or changed so that the operation call site can be
   certified?

3. Should a generic-fallback operation be allowed to become
   `DirectStateGet/Set` if:
   - it is compiler-certified as a known state operation,
   - a matching active runtime state frame exists,
   - the operation visibility is legacy bridge,
   - but no `candidate_handler` exists in the current operation object?

4. If the answer to 3 is no, how do we get a non-legacy visibility proof for
   local-ref known operations?
   - Should specialize/runtime evidence carry an explicit known-operation route?
   - Should lowering attach a handler/capability identity to the local-var
     operation call?
   - Should Evidence VM construct a provider-grant-style proof from the known
     handler catch entry?
   - Or is the current operation/call/provider model missing a concept?

5. What is the correct proof object for Stage D?

   Candidate shape:

   ```rust
   struct KnownStateOperationRouteProof {
       operation_call: ExprId,
       callee: ExprId,
       plan_id: EvidenceVmKnownHandlerPlanId,
       handler_id: u32,
       role: StateGet | StateSet,
       allowed_set_id: EvidenceVmAllowedSetId,
       route_kind: StaticKnownHandler | ProviderGrantKnownHandler,
       hygiene_baseline: ...?,
   }
   ```

   Is this close, or should the proof be shaped differently?

6. Where should this proof be produced?

   Please evaluate:

   - lowering
   - specialize/runtime evidence surface
   - Evidence VM object plan
   - runtime route lookup
   - catch entry / active state frame stack

7. Where should the direct execution run?

   Current effect-op application flow creates an effect thunk and later force
   produces a request. Should `DirectStateGet/Set` happen:

   - at effect-op application,
   - when forcing the effect thunk,
   - in `effect_route_for_operation_call`,
   - as a new continuation frame after payload evaluation,
   - somewhere else?

   Please preserve existing payload evaluation order.

8. What exactly should the runtime guard check?

   For example:

   - active frame with `plan_id`
   - active frame is inside the same dynamic handler/catch identity
   - handler/capability identity matches
   - operation role matches get/set
   - marker/provider/hygiene proof is still valid
   - no dirty provider grant / shadowing
   - payload shape/arity is valid

   Which of these are necessary, and where are they available?

9. What should happen on guard failure?

   - generic request fallback?
   - direct route disabled at plan time?
   - debug assertion?
   - runtime error?

10. How should continuation snapshot/fork interact with Stage D?

    Current Stage B only pushes a runtime state frame and has canaries. It does
    not yet explicitly store state frames inside captured continuations.

    Is it safe to enable route-specific direct state ops before explicit
    state-frame snapshots exist, given the env-shadow compatibility path?

    Or must explicit state-frame snapshots/forks be implemented first?

11. What are the minimal canaries before enabling Stage D?

    Please include cases involving:

    - simple local `get/set`
    - set before and after nondet resume
    - continuation captured inside state handler and resumed twice
    - same-family nested state handlers / shadowing
    - escaped `&x`
    - callback/provider boundary if relevant

12. Which implementation path should be explicitly avoided?

    I am especially worried about:

    - "if active state frame exists, just use it"
    - source path equality as the main proof
    - treating compiler local refs as VM cells
    - bypassing payload evaluation
    - adding ad hoc marker-stack-empty shortcuts

## Desired output format

Please structure the answer as:

1. Short verdict: whether Stage D can be safely implemented now.
2. Missing proof, stated precisely.
3. Required IR/plan/runtime data changes.
4. Runtime algorithm for direct `get`.
5. Runtime algorithm for direct `set`.
6. Guard failure fallback rules.
7. Required counters.
8. Required canaries.
9. Staged implementation plan with rollback points.
10. Things not to do.

## Constraints

- Do not rely on benchmark names, file paths, source names, std function paths,
  or string matching as runtime proof.
- Do not suggest using `Any` as a type inference fallback. In Yulang, `Any` is
  top, `Never` is bottom, and `Unknown` is the only unknown type.
- Public `std.control.var.ref` must remain a normal abstraction.
- User-defined refs, file refs, and projected refs must keep using the generic
  protocol unless separately certified.
- Handler hygiene / marker / provider semantics must not be weakened.
- If a plan changes multi-shot state semantics, say so explicitly.
- Prefer cause-side IR/runtime changes over downstream output patching.
