# ChatGPT Pro consultation: Evidence VM general handler speedup after known-state

Paste the answer here:

- `notes/research/consultation/2026-06-30-evidence-vm-general-handler-speedup-answer.md`

## Question

Please answer in Japanese.

I am working on Yulang, a language with algebraic effects, effect rows, handlers,
and an interpreter called Evidence VM. I need an architecture-level review and a
concrete staged plan. Please avoid small benchmark-specific tricks.

The previous consultation recommended a Koka-style `KnownHandlerPlan::State`
architecture, with the first producer being compiler-generated local mutable
variables. I implemented the first slices. The catastrophic 2-second local-ref
loop is now much better, but the remaining cost is still too high, and I want
the next step to be a general mechanism rather than local-variable-only
specialization.

## Current implementation status

Already implemented:

- `EvidenceVmKnownHandlerPlan::State`
- compiler-local-var certificate producer
- known state handler object/debug surfaces
- runtime known-state lookup indexed by catch expression
- direct execution for certified local state `get` / `set` after the operation
  reaches the catch boundary and passes the existing visibility check
- counters:
  - `plan_known_state_handlers`
  - `plan_known_state_handler_compiler_certificates`
  - `known_state_direct_gets`
  - `known_state_direct_sets`
  - `known_state_direct_missing_state`
  - `known_state_direct_non_resumptive`
  - `ref_set_*`

Important limitation:

- The current direct state execution happens late, at the generic request /
  catch boundary.
- `direct_effect_calls` is still `0`.
- Operation objects for these calls are still shown as `generic-fallback`.
- So this is not yet route-specific direct state op execution.

Current design note:

- `notes/design/2026-06-30-known-state-handler-plan.md`

Current committed state:

- commit: `680d4cbc Add known state handler direct execution`

## Current measurements

Built with:

```sh
timeout 240s cargo build -q --release -p yulang
```

Representative no-cache release runs:

```sh
target/release/yulang --no-cache run --runtime-phase-timings --print-roots <file>
```

Results:

- `bench/loop_for_no_ref_20_discard.yu`
  - nested std `for`, no mutable ref
  - `run.runtime_execute: 6.4ms`
  - `expr_evals: 49077`
  - `env_clones: 33120`
  - `list_merge_calls: 0`

- `bench/loop_for_sum_ref_20_discard.yu`
  - nested std `for`, `my $total = 0`, `&total = $total + i + j`
  - `run.runtime_execute: 50.3ms`
  - `expr_evals: 58718`
  - `env_clones: 52815`
  - `known_state_direct_gets: 800`
  - `known_state_direct_sets: 400`
  - `ref_set_evals: 400`
  - `ref_set_update_effect_calls: 400`
  - `ref_set_assignment_ref_update_requests: 400`
  - `list_merge_calls: 0`

- `bench/loop_for_20_discard.yu`
  - nested std `for`, `my $xs = []`, `&xs.push(i + j)`
  - `run.runtime_execute: 75.5ms`
  - `expr_evals: 60723`
  - `env_clones: 53218`
  - `known_state_direct_gets: 800`
  - `known_state_direct_sets: 400`
  - `ref_set_evals: 400`
  - `ref_set_update_effect_calls: 400`
  - `ref_set_assignment_ref_update_requests: 400`
  - `list_merge_calls: 400`

- `bench/nondet_20_discard.yu`
  - `(each 1..20 + each 1..20).list`
  - `run.runtime_execute: 10.1ms`
  - `expr_evals: 37028`
  - `env_clones: 26567`
  - `list_merge_calls: 420`

Reading:

- Known-state direct execution fixed the catastrophe, but local-ref `for` is
  still about 8x slower than `for` without refs.
- List accumulation via `&xs.push` is slower still because it combines local
  state with list merge.
- `nondet` has similar list merge counts, but remains much faster than
  `for + local ref + push`, so list merge is not the only issue.
- `env_clones` is high, but `Env` is already a persistent one-binding chain, so
  this is not a full environment copy.

## Failed short trials

I tried two conservative general-routing ideas and reverted them because they
did not improve the representative benchmarks.

### Trial 1: catch-body provider env

Idea:

- Build a provider env from handler objects for each catch expression.
- Wrap catch body evaluation in `with_provider_env`.
- Reuse the existing provider-grant route machinery instead of special-casing
  variable names.

Result:

- Tests passed.
- Representative `loop_for_sum_ref_20_discard` had unchanged counters:
  - `expr_evals: 58718`
  - `env_clones: 52815`
  - `known_state_direct_gets: 800`
  - `known_state_direct_sets: 400`
- Runtime did not improve.

Likely reading:

- The hot operation calls still reach the handler through generic request /
  continuation machinery.
- Simply placing a provider env around the catch body does not make the op-call
  route-specific at the actual operation execution point.

### Trial 2: active-handler direct route when markers are empty

Idea:

- At operation route lookup, if:
  - active provider handler ids are present,
  - active marker/add-id/handler-frame stacks are empty,
  - operation-provider lookup has a matching handler candidate,
  then use a request-free direct route.

Result:

- Tests passed.
- Representative counters were still unchanged.
- Runtime got slightly worse/noisy.

Likely reading:

- This route was not on the hot path, or the relevant operations were not in a
  shape where this conservative guard applied.

Both trials were reverted. I do not want to accumulate dormant complexity unless
it has a clear route to payoff.

## What I need

Please propose the next real plan.

The main question:

> What is the next principled, general Evidence VM optimization after the first
> known-state handler direct execution?

Please evaluate at least these options:

1. Route-specific direct state op execution
   - compile certified `get` / `set` call sites to direct op execution before
     generic request allocation
   - preserve marker/provider/hygiene semantics
   - avoid name/path string matching

2. General known-handler frame execution
   - not only state handlers, but a framework for certified handler operations
   - possibly derived from evidence routes plus handler certificates

3. Ref protocol optimization
   - keep public `std.control.var.ref` generic
   - but optimize `RefSet` / `update_effect` / `ref_update` for certified local
     state refs or certified lens/projection refs
   - avoid turning this into a local-variable-only cell special case

4. Iterator / `for` IR
   - std `for` without refs is 6ms vs pure recursive loops around 1.5ms
   - should this be handled by a direct iterator IR, or after handler/ref work?

5. List merge / builder optimization
   - `list_merge_calls` appears in `nondet` and `&xs.push`
   - but `nondet` is much faster than `for + ref + push`
   - should list work wait, or is a builder/fusion plan important now?

6. More continuation/scope executor work
   - previous ScopePlan work made nondet fast
   - is the remaining local-ref cost still continuation/catch/resume machinery,
     or now mostly `RefSet` protocol overhead?

## Specific questions

1. What is the most likely bottleneck behind the remaining `50ms` local-ref sum
   case, given that certified `get/set` are already directly executed at the
   catch boundary?
2. Is late catch-boundary direct state execution enough architecturally, or must
   we add route-specific direct state opcodes to avoid generic request creation?
3. What exact control/runtime IR should be introduced next, if any?
   - `DirectStateGet`
   - `DirectStateSet`
   - `KnownOperationCall`
   - `KnownHandlerFrame`
   - something else
4. Where should the proof live?
   - lowering certificate
   - specialize/runtime evidence surface
   - evidence-vm plan
   - runtime guard
5. How should marker/provider hygiene be preserved for route-specific direct
   state operations?
6. How should continuation capture and multi-shot resume handle state frames if
   the state op no longer goes through generic catch recursion?
7. Is it safe to optimize `RefSet` directly for certified local state refs, or
   would that be a problematic special case?
8. How can escaped `&x` remain fast without turning all refs into VM cells?
9. What are the smallest canaries that must be added before route-specific state
   ops or ref protocol shortcuts?
10. Which path should be explicitly avoided because it looks attractive but will
    cause special-case accumulation or hygiene bugs?

Please rank the next implementation candidates by:

- semantic risk
- expected performance gain
- implementation size
- fit with algebraic-effect semantics
- likelihood of becoming a reusable optimization framework

Please give a staged plan with rollback points and concrete counters to add.

## Constraints

- Do not rely on benchmark names, file paths, source names, std function paths,
  or string matching.
- Do not suggest using `Any` as a type inference fallback. In Yulang, `Any` is
  top, `Never` is bottom, and `Unknown` is the only unknown type.
- Public `std.control.var.ref` must remain a normal abstraction.
- User-defined refs, file refs, and projected refs must keep using the generic
  protocol unless separately certified.
- Handler hygiene / marker / provider semantics must not be weakened.
- If a plan changes multi-shot state semantics, say so explicitly.
- Prefer cause-side IR/runtime changes over downstream output patching.
