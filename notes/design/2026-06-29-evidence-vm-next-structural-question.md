# Evidence VM next structural performance question

This is a question sheet for the next Evidence VM performance review.

The context has changed since the earlier single-digit question: the Evidence
VM is now the default runtime route, `bench/nondet_20_discard.yu` reaches
single-digit runtime in `debug evidence-vm-run`, and the remaining question is
what structural work is still worth doing.

Please focus on the next runtime design step, not on local micro-optimizations
unless they clearly unblock the structural step.

## Current baseline

Commit:

- `848a0362`

Recent release measurements using `target/release/yulang` and a warm
source-key cache:

### `debug evidence-vm-run --compare-control bench/nondet_20_discard.yu`

Five runs:

- `timing.runtime_evidence_execute`: `9.1ms / 8.8ms / 8.8ms / 9.1ms / 9.2ms`
- `timing.total_before_compare`: `11.0ms / 10.4ms / 10.3ms / 10.5ms / 10.8ms`
- all runs: `compare.control: match`

### `debug evidence-vm-run --compare-control examples/showcase.yu`

Three runs:

- `timing.runtime_evidence_execute`: `21.0ms / 19.8ms / 18.7ms`
- later `timing.total_before_compare`: `22.8ms / 21.4ms`
- all runs: `compare.control: match`

### Normal `run --runtime-phase-timings --print-roots`

`bench/nondet_20_discard.yu`, source-key hit:

- `run.runtime_execute`: `10.2ms-11.4ms`
- `run.total`: `12.4ms-13.7ms`

`examples/showcase.yu`, source-key hit:

- `run.runtime_execute`: `24.2ms-25.5ms`
- `run.total`: `28.4ms-29.6ms`

Small examples are already quite light after source-key cache hit:

- `examples/03_for_last.yu`: `run.total` about `2.3ms-2.4ms`
- `examples/02_refs.yu`: `run.total` about `1.5ms`

## Current hot counters

Representative `bench/nondet_20_discard.yu` counters:

- `expr_evals: 37028`
- `env_clones: 26567`
- `env_entries_cloned: 0`
- `apply_value_calls: 16641`
- `primitive_apply_calls: 2123`
- `forced_effect_call_fusions: 861`
- `thunk_forces: 4789`
- `continuation_appends: 6321`
- `continuation_resume_steps: 21566`
- `continuation_resume_then_steps: 2562`
- `continuation_resume_force_steps: 11781`
- `continuation_resume_catch_steps: 840`
- `continuation_resume_marker_steps: 1680`
- `continuation_resume_provider_steps: 1722`
- `catch_body_checks: 2962`
- `catch_boundary_direct_tail_signals: 861`
- `catch_boundary_generic_request_signals: 399`
- `marker_frame_entries: 13526`
- `active_add_id_scans: 1995`
- `function_call_marker_plans: 11448`
- `list_merge_calls: 420`

Representative `examples/showcase.yu` counters:

- `expr_evals: 123522`
- `env_clones: 86078`
- `env_entries_cloned: 0`
- `apply_value_calls: 56728`
- `primitive_apply_calls: 7015`
- `forced_effect_call_fusions: 2457`
- `thunk_forces: 12212`
- `continuation_appends: 12523`
- `continuation_resume_steps: 26491`
- `continuation_resume_then_steps: 5251`
- `continuation_resume_force_steps: 6793`
- `continuation_resume_catch_steps: 1644`
- `continuation_resume_marker_steps: 3338`
- `continuation_resume_provider_steps: 3568`
- `catch_body_checks: 6577`
- `catch_boundary_direct_tail_signals: 1791`
- `catch_boundary_generic_request_signals: 682`
- `marker_frame_entries: 40967`
- `active_add_id_scans: 3421`
- `function_call_marker_plans: 41054`
- `list_merge_calls: 832`

Important reading:

- `env_clones` is large, but `env_entries_cloned = 0`, so this appears to be
  mostly cheap structural sharing rather than large environment copying.
- `marker_frame_entries`, `function_call_marker_plans`, `continuation_resume_*`,
  and `catch_body_checks` look like the remaining structural costs.
- Control VM is now slower on the representative effect-heavy workloads. It may
  still contain small ideas, but direct migration from Control VM does not look
  like the main path.

## Important accepted runtime work

The Evidence VM already has permission-native direct-tail close paths:

- `NativeProviderPair`
- `NativeProviderPrefixBoundary`
- `NativeProviderEnvForeignBoundary`

These are documented in:

- `notes/design/evidence-vm-native-close-invariants.md`

The native branches are intentionally narrow. In particular:

- prefix boundary and provider-env foreign boundary are separate certs
- nearest ProviderEnv miss is not evidence of invisibility
- later ProviderEnv grant matched legacy visible behavior, but the attempted
  native close was slower, so it remains profile-only

The old `provider_env_then_compaction_*` profile has now been removed from the
runtime stats surface. It falsified the exact same-ProviderEnv collapse
hypothesis:

- no exact same-ProviderEnv candidate appeared in nondet/showcase
- adjacent ProviderEnv frames existed but carried different environments

## Changes that helped recently

- Evidence VM became the default runtime route.
- path / route lookup surfaces were made dense where useful.
- direct-tail native close branches were added with explicit certs.
- rejected later-grant traversal was gated behind `--runtime-evidence-profile-deep`.
- stale `provider_env_then_compaction_*` counters were removed.
- old `has_request_boundary` bool helper was removed; `request_boundary_profile`
  is now the remaining request-boundary diagnostic surface.

## Changes that did not help or are risky

- exact same ProviderEnv collapse
  - no candidates in representative workloads
- later ProviderEnv grant native close
  - visible semantics matched, but the fast path was slower
- duplicate marker scope skip
  - reduced marker frame entries, but the cover checks and resulting shape cost
    more than they saved
- stats-off fast path
  - possible, but broad; many plain counters are scattered through the runtime
  - likely not the first structural move unless there is a clean design
- treating nearest ProviderEnv miss as invisible
  - falsified by shadow runs
- arbitrary `any ProviderEnv` grant
  - too coarse to be used as permission evidence

## Candidate next directions

I want advice on which of these is now worth doing.

### A. Port remaining Control VM tricks

Maybe there are still useful ideas in Control VM. But the obvious ones already
seem absorbed or surpassed by Evidence VM:

- path lookup / route tables
- marker scan avoidance
- direct handler route
- list merge improvements
- native close for direct-tail paths

Question: is there still a specific Control VM trick worth porting, or is this
now mostly a dead end?

### B. Stats-off fast runtime API

Normal `run` currently returns stats even when `--runtime-phase-timings` is not
requested. That means basic counters still increment in normal runtime.

Potential idea:

```rust
run_program_with_plan_fast(...)
```

or a runtime context flag that disables ordinary counters unless phase timings
or debug reporting needs them.

Concern:

- counter increments are spread across the runtime
- gating all of them may add branches or make the code harder to read
- the performance win may be smaller than expected

Question: is this worth doing now? If yes, what is the least intrusive design?

### C. Marker/call boundary representation

`function_call_marker_plans` and `marker_frame_entries` are still large.
`EvidenceActiveMarkerPlan` already caches `function_call_markers` with
`OnceCell`, so the obvious marker transformation is probably not being rebuilt
every time.

The remaining cost may be:

- entering marker frames
- pushing active marker plans
- closing marked results
- repeatedly applying call-boundary marker logic around ordinary calls

Question: is there a safe structural rewrite that turns function-call marker
boundaries into a lighter state transition without weakening hygiene?

### D. CatchBody / ResumePlan / ScopeDelta structural rewrite

Previous advice suggested moving from the continuation tree toward something
like:

```text
ResumePlan {
  eval_segment,
  request_boundary_delta,
  handler_boundary_delta,
  marker_delta,
  provider_delta,
  route_cert,
  multiplicity,
}
```

The idea is not to flatten scopes, but to move scope/evidence deltas out of the
ordinary continuation spine.

Question: is this still the main structural direction after the recent speedups,
or is it now too much engineering for the remaining 10-25ms range?

### E. Continue with native backend / bytecode / compiled blocks

Evidence VM is now fast enough for many normal uses. If the goal is a much
larger jump, perhaps the correct next step is not another tree-runtime rewrite,
but a compiled representation:

- bytecode blocks
- direct-style pure/eval islands
- explicit scope opcodes
- native or Cranelift later

Question: should runtime work now move toward a compiled block representation,
or should Evidence VM first be simplified further?

## Constraints

Any recommendation must preserve:

- `--compare-control` equality
- handler hygiene
- permission-native close invariants
- adversarial corpus behavior
- no path/name/test-specific branches

Do not recommend:

- widening native close branches without shadow stats and a separate cert
- treating ProviderEnv miss as invisibility
- using arbitrary `any ProviderEnv` as permission evidence
- flattening `Then` / `MarkerFrame` / `ProviderEnv` without a scope-preserving
  invariant
- weakening generic request fallback as the safety surface

## Questions to answer

1. What is the next best structural step from this state?
2. Should I spend time on Control VM trick migration, or skip it?
3. Is a stats-off fast runtime API likely worth the complexity?
4. Is the remaining cost more likely in marker/call boundary handling, catch
   boundary handling, or generic continuation resume?
5. If the answer is a structural rewrite, what is the smallest first patch that
   gives a meaningful signal?
6. What falsification criteria should I use before abandoning that direction?

## Desired answer format

Please answer with:

- recommended priority order
- expected performance impact
- semantic risk
- first implementation slice
- counters to watch
- stop / rollback criteria

## Pro response

### Recommended priority order

| Priority | Direction                                                                  | Call                                                                 |
| -------: | -------------------------------------------------------------------------- | -------------------------------------------------------------------- |
|        1 | **D. CatchBody-aware ResumePlan / ScopeDelta rewrite**                     | Main next step                                                       |
|        2 | **C. Marker/call boundary representation, but only as part of ResumePlan** | Do after / inside #1                                                 |
|        3 | **B. Stats-off fast API**                                                  | Defer; useful only if branchless and small                           |
|        4 | **E. Compiled block / bytecode path**                                      | Prepare via ResumePlan IR; do not jump straight to native            |
|        5 | **A. Control VM trick migration**                                          | Mostly skip; use as design reference and oracle, not a porting queue |

The next best structural move is **not another native-close branch** and not a local marker skip. It is a **sidecar `ResumePlan` representation for resumed/direct-tail continuations where ordinary eval frames and scope/evidence deltas are separated**.

The key point: the current runtime has `Then`, ordinary eval frames, `CatchBody`, `MarkerFrame`, and `ProviderEnv` all inside the same `EvidenceContinuationFrame` tree. `CatchBody`, `MarkerFrame`, and `ProviderEnv` are semantically necessary, but keeping them on the ordinary resume spine forces repeated tree walking, repeated boundary checks, and repeated marker/provider re-entry. The enum shape makes that visible directly.

The goal should be:

```rust
ResumePlan {
    eval: EvalSegment,
    request: RequestBoundaryDelta,
    handler: HandlerBoundaryDelta,
    marker: MarkerDeltaId,
    provider: ProviderDeltaId,
    route: EvidenceRouteCert,
    multiplicity: ContinuationMultiplicity,
}
```

This is **not scope flattening**. It is scope-preserving extraction: the scope/evidence operations still occur in the same semantic order, but they are no longer ordinary continuation frames that every resume path must rediscover.

---

### Expected performance impact

| Work                                             |                            Expected impact | Why                                                                                                              |
| ------------------------------------------------ | -----------------------------------------: | ---------------------------------------------------------------------------------------------------------------- |
| CatchBody-aware ResumePlan shadow only           |                    0% runtime, high signal | Measures coverage and rejection reasons                                                                          |
| Narrow ResumePlan execution slice                |            **5–15%** if coverage is decent | Cuts repeated tree resume and `Then` churn on selected paths                                                     |
| ResumePlan + MarkerDelta/ProviderDelta execution | **15–35%** on nondet/showcase is plausible | Attacks `continuation_resume_*`, `marker_frame_entries`, `function_call_marker_plans`, and append churn together |
| Stats-off API                                    |                **1–5%** likely, maybe less | Counter increments exist, but they are not the structural shape cost                                             |
| Bytecode/native backend                          |                   Potentially larger later | But only after ResumePlan gives a clean block/scope IR                                                           |

I would not expect another narrow native close to move the representative workloads much. The accepted native-close rules are intentionally certificate-based and narrow; the invariants explicitly require fallback for value results, generic requests, routed yields, handler-path cases, carry-after-frame markers, legacy bridges, and resume deltas.

The later ProviderEnv grant result is especially important: visible behavior matched legacy, but the native branch was slower, and the note says not to re-enable it until the **continuation representation** becomes cheaper. That points away from widening close rules and toward the ResumePlan/ScopeDelta rewrite.

---

### Semantic risk

| Direction                            | Semantic risk                             | Notes                                                                                        |
| ------------------------------------ | ----------------------------------------- | -------------------------------------------------------------------------------------------- |
| ResumePlan shadow builder            | Low                                       | No behavior change; just classification                                                      |
| CatchBody-aware ResumePlan execution | Medium-high                               | Handler visibility, generic fallback, and multi-shot continuation behavior must remain exact |
| MarkerDelta execution                | High if done alone; medium if plan-backed | Hygiene can be weakened accidentally if marker scopes are treated like removable wrappers    |
| ProviderDelta execution              | High                                      | ProviderEnv miss/grant/later-grant distinctions must remain explicit                         |
| Stats-off API                        | Low semantic, medium maintenance          | Easy to make code noisy or accidentally branchy                                              |
| Bytecode/native backend              | High engineering + semantic risk          | Bad idea before the runtime IR is clean                                                      |

The safety rail is simple: **generic request fallback remains the truth surface**. A new plan path may skip tree walking only when it has enough explicit evidence to reproduce the old path. Anything not proved falls back.

---

### Where the remaining cost probably is

It is not one bucket. The best reading is:

```text
raw hot count:
  marker/call boundary handling

structural blocker:
  CatchBody / request boundary

mechanism that pays the bill:
  generic continuation resume over a mixed frame tree
```

For `showcase`, `marker_frame_entries` and `function_call_marker_plans` are the obvious raw heat. For `nondet`, `continuation_resume_force_steps`, `continuation_resume_then_steps`, direct-tail/generic request interaction, and catch boundary checks are more visible. But the deeper problem is that the same continuation tree carries both eval work and scope/evidence boundaries.

That shows up in the code too: `resume_continuation` recursively destructures the tree, handles `Then` by resuming the first continuation and then continuing with the second, and handles `CatchBody`, `MarkerFrame`, and `ProviderEnv` as normal frames in the same dispatch.

Also, the current direct-tail segment profile treats `CatchBody` and ref-set handler frames as request boundaries, and the segment profile can only shadow a segment when `request_boundaries == 0`. So a plain “eval segment” pass is likely to keep bouncing off CatchBody unless CatchBody becomes a first-class request delta.

So the answer to question 4 is:

1. **Marker/call boundary handling** is the largest visible local cost.
2. **CatchBody/request boundary handling** is the structural blocker.
3. **Generic continuation resume** is the broad execution mechanism that makes both expensive.

That means the first structural patch should be **CatchBody-aware ResumePlan**, not “marker skip v2”.

---

### Control VM trick migration

Skip broad Control VM trick migration.

The useful Control VM idea has already been absorbed at the level that matters: **resume as data, not closure wrapping**. The old Control VM plan was motivated by request resume closures being repeatedly wrapped through marker/catch paths; Evidence VM already has a data continuation tree instead.

There may still be small ideas worth stealing later:

```text
- frame-loop execution style
- direct known callee dispatch
- primitive direct fast paths
- compact block/eval segments
```

But those are not the next structural win. Porting them directly risks reintroducing a second runtime architecture without attacking the current mixed-spine problem.

Use Control VM for:

```text
- parity tests
- adversarial behavior comparison
- vocabulary for “frame loop” / “segment”
```

Do not use it as a migration checklist.

---

### Stats-off fast runtime API

Not now.

There is already a partial split: `runtime_breakdown_stats_enabled` gates some detailed counters, and it is enabled for debug builds or deep profile.  But the normal run output always carries `evidence_stats`, and plain counters still increment in hot helpers like `record_continuation_append`.

A stats-off API is worth doing only if it is **branchless on the hot path**. A runtime flag like this:

```rust
if stats_enabled {
    self.stats.expr_evals += 1;
}
```

spread everywhere is probably the wrong shape. It adds branches and makes the runtime harder to read.

The least intrusive good design would be a small instrumentation abstraction:

```rust
trait EvidenceRuntimeStatsSink {
    #[inline(always)]
    fn inc_expr_evals(&mut self);
    #[inline(always)]
    fn inc_apply_value_calls(&mut self);
    #[inline(always)]
    fn inc_continuation_resume_steps(&mut self);
    #[inline(always)]
    fn breakdown_enabled(&self) -> bool;
    fn finish(self) -> RuntimeEvidenceRunStats;
}

struct CollectStats {
    stats: RuntimeEvidenceRunStats,
}

struct NoStats;
```

Then the runner can be monomorphized:

```rust
RuntimeEvidenceRunner<CollectStats>
RuntimeEvidenceRunner<NoStats>
```

That keeps the fast path branchless after inlining. But it is still a broad refactor, and the likely win is smaller than the ResumePlan work.

Do this later, after the structural work has made the hot path clearer.

---

### First implementation slice

The smallest useful first patch is:

## Patch 1: `ResumePlanCandidate` shadow builder

No execution change. Build a real candidate object beside the old continuation tree, then discard it.

Not just counters; build enough structure to prove the representation can encode the old continuation:

```rust
enum ResumePlanCandidate {
    Planned {
        eval_frames: SmallVec<[EvalFrameKind; 8]>,
        request: RequestBoundaryDelta,
        marker: MarkerDeltaShadowId,
        provider: ProviderDeltaShadowId,
        route: EvidenceRouteCert,
        multiplicity: ContinuationMultiplicity,
    },
    Rejected(ResumePlanReject),
}

enum RequestBoundaryDelta {
    None,
    CatchSameHandler {
        catch_expr: ExprId,
    },
    CatchForeignHandler {
        catch_expr: ExprId,
    },
    CatchNoRoutedHandler {
        catch_expr: ExprId,
    },
    RefSet,
}

enum ResumePlanReject {
    UnsupportedFrame,
    RefSetBoundary,
    ForeignCatchNeedsTree,
    DynamicMarkerUnsupported,
    ProviderDeltaUnsupported,
    LegacyBridge,
    ResumeDelta,
}
```

Build it at the same sites where the runtime already has meaningful continuation materialization:

```text
- continuation thunk creation / application
- DirectTail continuation append
- routed/generic request continuation append
- resume-pack candidate recording
```

Keep execution on the old tree.

The point of this patch is to answer:

```text
Can most hot continuations be represented as:
  EvalSegment + RequestBoundaryDelta + MarkerDelta + ProviderDelta
without inventing a new semantic rule?
```

If yes, proceed to execution. If no, stop before doing a large rewrite.

---

## Patch 2: intern real marker/provider deltas, still no execution

The runtime already has shadow-key machinery for marker/provider deltas, so the next slice is to turn that into an actual reusable table:

```rust
struct MarkerDelta {
    enter_ops: Rc<[MarkerEnterOp]>,
    active_add_id_ops: Rc<[AddIdEnterOp]>,
    handler_boundary_ops: Rc<[HandlerBoundaryEnterOp]>,
}

struct ProviderDelta {
    frames: Rc<[ProviderDeltaFrame]>,
}
```

Do **not** try to skip duplicate marker scopes again. The previous failure mode is exactly the danger here: lowering the counter is not enough if the cover checks and resulting shape cost more. The win condition is lower wall time and lower resume/marker work, not just lower `marker_frame_entries`.

---

## Patch 3: execute one narrow planned path

Only after Patch 1 shows high coverage.

First executable subset:

```text
- no RefSet boundary
- request delta is None or CatchSameHandler
- marker/provider deltas are representable by interned deltas
- no legacy bridge
- no resume-delta unless explicitly represented
- multi-shot continuation uses immutable plan data
- fallback keeps old tree intact
```

The first executable path should still be conservative. It can materialize back to the old continuation tree on any unsupported edge. The first goal is not maximum speed; it is proving that `ResumePlan` execution can reduce resume steps without changing control equality.

---

### Counters to watch

Existing counters:

```text
timing.runtime_evidence_execute
timing.total_before_compare
compare.control

continuation_resume_steps
continuation_resume_then_steps
continuation_resume_force_steps
continuation_resume_catch_steps
continuation_resume_marker_steps
continuation_resume_provider_steps

continuation_appends
continuation_append_steps
request_continuation_appends
direct_tail_continuation_appends
request_whole_continuation_appends

catch_body_checks
catch_boundary_entries
catch_boundary_direct_tail_signals
catch_boundary_generic_request_signals
direct_tail_blocked_by_catch_boundary

marker_frame_entries
function_call_marker_plans
active_marker_plan_pushes
active_marker_plan_dedupes
resume_marker_plan_dynamic_scope
resume_marker_plan_enter_ops_total
active_add_id_scans

route_cert_provider_grant_clean
route_cert_provider_grant_dirty_add_id
route_cert_provider_grant_dirty_handler
route_cert_provider_grant_dirty_scope
```

Add new counters:

```text
resume_plan_candidates
resume_plan_planned
resume_plan_rejected

resume_plan_reject_ref_set
resume_plan_reject_foreign_catch
resume_plan_reject_dynamic_marker
resume_plan_reject_provider_delta
resume_plan_reject_legacy_bridge
resume_plan_reject_resume_delta
resume_plan_reject_unsupported_frame

resume_plan_eval_frames
resume_plan_request_delta_none
resume_plan_request_delta_catch_same
resume_plan_request_delta_catch_foreign
resume_plan_request_delta_catch_no_routed
resume_plan_marker_delta_unique
resume_plan_marker_delta_reused
resume_plan_provider_delta_unique
resume_plan_provider_delta_reused

resume_plan_exec_hits
resume_plan_exec_tree_fallbacks
resume_plan_exec_saved_resume_steps_estimate
resume_plan_exec_materialized_tree_fallbacks
resume_plan_shadow_mismatches
```

The most important new metric is not candidate count. It is:

```text
planned weighted by old continuation_resume_steps
```

A plan that covers many cold continuations is noise. A plan that covers the continuations responsible for most `Then` / marker / provider / catch resume steps is valuable.

---

### Stop / rollback criteria

Rollback immediately if any of these happen:

```text
- --compare-control mismatch
- adversarial corpus mismatch
- generic request fallback behavior changes
- handler hygiene tests regress
- native close mismatch / shadow mismatch appears
- ProviderEnv miss starts being used as invisibility evidence
- any ProviderEnv presence starts being used as permission evidence
```

Abandon or pause the ResumePlan direction if Patch 1 shows:

```text
resume_plan_planned / resume_plan_candidates < 40% on weighted hot steps
```

or if most rejections are structural and unavoidable:

```text
- foreign catch dominates
- RefSet boundary dominates
- dynamic marker/provider deltas cannot be encoded without rebuilding the old tree
```

Rollback the first execution slice if:

```text
- runtime_evidence_execute improves by less than ~5% on both nondet_20_discard and showcase
  while code complexity rises substantially

- continuation_resume_steps drops but marker_frame_entries / active_add_id_scans / generic request signals rise enough
  to erase wall-time improvement

- direct-tail signals fall and generic request signals rise

- branch count / allocation count increases in small examples
```

For stats-off API, abandon if:

```text
- branchless NoStats runner gives less than ~3% on nondet/showcase
- any flag-based implementation slows normal release runs
- the refactor makes counter sites harder to audit before ResumePlan lands
```

For bytecode/native backend, defer until:

```text
- ResumePlan or equivalent scope-delta IR exists
- pure/eval segment boundaries are explicit
- marker/provider/request deltas have a compact representation
```

Otherwise bytecode will just compile the current tree-walking shape.

---

### Final recommendation

Do **D first**, but as a narrow sidecar:

```text
CatchBody-aware ResumePlan shadow
→ real MarkerDelta / ProviderDelta interning
→ narrow ResumePlan execution
→ only then bytecode/compiled blocks
```

Skip Control VM migration except as a reference. Defer stats-off until the runtime shape is cleaner. Treat marker/call boundary work as part of the ResumePlan rewrite, not as another local marker optimization.

The next meaningful structural target is:

```text
move CatchBody / MarkerFrame / ProviderEnv out of the ordinary continuation spine
without flattening their scopes
```

That is the path most likely to turn the remaining 10–25ms range into a clearly lower plateau while preserving control equality and hygiene.
