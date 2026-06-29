## 0. Current reading

The next profitable work is **not** another broad direct-route widening, not `ProviderEnv` flattening, and not a stats-off sweep.  The accepted work has already moved Evidence VM into the default runtime path, brought `bench/nondet_20_discard.yu` into the single-digit / low-10ms range, and added a narrow `CatchForeign ScopePlan` direct-tail compact signal executor.

The remaining work should focus on **scope-preserving continuation execution**:

```text
DirectTail / ResumePlan / ScopePlan
  = eval lane
  + request/catch boundary lane
  + marker delta lane
  + provider delta lane
  + exact fallback-to-tree surface
```

The immediate next step is a **measured direct-tail scoped-delta executor v2** that consumes the existing scoped trace / delta payload more directly, without turning the current compact signal path into a broad value executor.

---

## 1. Ground rules

### Must preserve

- `debug evidence-vm-run --compare-control` equality.
- `cargo test -q -p evidence-vm -- --test-threads=1`.
- `cargo test -q -p yulang runtime_evidence -- --test-threads=1`.
- `tests/yulang/yulang-adversarial-corpus/probe.sh`.
- Native close invariants:
  - `NativeProviderPair`
  - `NativeProviderPrefixBoundary`
  - `NativeProviderEnvForeignBoundary`
- Generic request fallback as the truth surface.
- Handler hygiene and callback marker semantics.
- Exact distinction between:
  - nearest `ProviderEnv` grant
  - nearest `ProviderEnv` miss
  - later `ProviderEnv` grant
  - arbitrary `any ProviderEnv` presence

### Do not do

- Do not convert `LexicalHandlerCandidate` or `HygieneFallback` into `DirectHandlerCall`.
- Do not treat `ProviderEnv` miss as invisibility evidence.
- Do not use arbitrary `any ProviderEnv` as permission evidence.
- Do not flatten `Then` / `MarkerFrame` / `ProviderEnv` unless a scope-preserving invariant is explicit and shadowed.
- Do not resurrect later-grant native close without a new cert and a separate execution-shape fix.
- Do not reintroduce duplicate marker scope skip; it reduced counts but made wall time worse.
- Do not enable the existing value executor as-is; it regressed representative normal release paths.
- Do not start a bytecode/native backend before a compact scope-delta IR exists.

---

## 2. Baseline to capture before touching code

Run from a clean worktree, warm source-key cache, release binary.

```bash
cargo fmt --all --check
cargo check -q -p evidence-vm -p yulang
cargo check -q --release -p evidence-vm -p yulang
cargo build -q --release -p yulang
cargo test -q -p evidence-vm -- --test-threads=1
cargo test -q -p yulang runtime_evidence -- --test-threads=1
tests/yulang/yulang-adversarial-corpus/probe.sh
```

Representative runtime checks:

```bash
target/release/yulang --std-root lib debug evidence-vm-run --compare-control bench/nondet_20_discard.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control examples/showcase.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control --runtime-evidence-profile-deep bench/nondet_20_discard.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control --runtime-evidence-profile-deep examples/showcase.yu
target/release/yulang --std-root lib --runtime-phase-timings run --print-roots bench/nondet_20_discard.yu
target/release/yulang --std-root lib --runtime-phase-timings run --print-roots examples/showcase.yu
```

Record at least:

```text
git branch --show-current
git rev-parse --short HEAD
git status --short
runtime_evidence_execute / run.runtime_execute
compare.control
scope_exec_hits
scope_exec_tree_fallbacks
scope_exec_signal_passthrough_hits
scope_exec_value_resume_hits
scope_exec_reject_*
scope_plan_catch_foreign_boundary_delta_*_mismatch
continuation_appends
continuation_resume_steps
continuation_resume_then_steps
continuation_resume_force_steps
continuation_resume_catch_steps
continuation_resume_marker_steps
continuation_resume_provider_steps
marker_frame_entries
function_call_marker_plans
active_add_id_scans
expr_evals
env_clones
env_entries_cloned
thunk_forces
thunk_force_continuation
resume_pack_thunks_forced
catch_body_checks
catch_boundary_direct_tail_signals
catch_boundary_generic_request_signals
```

Suggested local summary table:

```text
| workload | mode | runs | median | min | max | compare | notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- |
| nondet_20_discard | debug evidence-vm-run | 5 | | | | match | |
| showcase | debug evidence-vm-run | 5 | | | | match | |
| nondet_20_discard | normal run | 5 | | | | n/a | source-key hit |
| showcase | normal run | 5 | | | | n/a | source-key hit |
```

---

## 3. Current known state to assume

### Accepted / useful

- Evidence VM is default route for normal `run`.
- `debug evidence-vm-run --compare-control` is the parity oracle.
- `--runtime-evidence-profile-deep` exists for expensive traversal/profile surfaces.
- `RuntimeEvidenceRunContext` already has `deep_profile` and rich stats.
- `EvidenceRouteCert`, `EvidenceEffectSignal`, `ResumeMarkerPlan`, resume/shadow/scope/catch counters already exist or have recently existed.
- `CatchForeign ScopePlan compact preserved tail` is accepted and `SCOPE_PLAN_FOREIGN_CATCH_EXECUTOR_ENABLED` should stay enabled unless a regression appears.
- `SCOPE_PLAN_FOREIGN_CATCH_VALUE_EXECUTOR_ENABLED` should stay disabled unless this plan’s value-executor investigation proves the overhead issue is solved.

### Observed recent performance range

Use current local measurements as truth, but expect this shape:

```text
bench/nondet_20_discard.yu:
  debug evidence-vm-run: often ~8.5ms–10ms
  normal run: often ~9.5ms–11.2ms with source-key hit

examples/showcase.yu:
  debug evidence-vm-run: often ~19.5ms–22ms
  normal run: often ~20.5ms–23ms with source-key hit
```

### Hot cost reading

The remaining hot path is a mixture of:

```text
1. continuation resume over mixed tree frames
2. marker/call boundary enter + close
3. CatchBody / foreign boundary pass-through
4. ProviderEnv restoration / preservation
5. ForceValueIfThunk and ordinary eval-frame dispatch
6. env clone count, mostly cheap because env_entries_cloned is usually 0
```

`env_clones` is large, but `env_entries_cloned = 0` means it is probably not the first structural target.

---

## 4. Main hypothesis

The next gain should come from making the accepted direct-tail ScopePlan path less tree-like.

Current accepted signal path still preserves semantics, but it can leave too much ordinary continuation machinery intact:

```text
ScopePlanForeignCatchBoundary(scope, boundaries)
  carried as compact tail
  still resumed through generic continuation dispatch later
```

The next executor should consume the scoped trace / delta payload directly for direct-tail signal pass-through:

```text
ScopedDirectTailDeltaExecutor
  reads root scope trace
  appends or carries compact eval/marker/provider/catch lanes
  avoids request-boundary profiling in accepted shapes
  avoids rebuilding old tree until fallback is needed
  materializes old continuation only on unsupported shape
```

This is not the same as the rolled-back value executor.  The target is the **direct-tail signal path**, where recent checks already showed high `scope_exec_signal_passthrough_hits` and zero mismatches.

---

## 5. Execution stages

### Stage 0 — Baseline and diff guard

Create or update this plan file first.  Then collect baseline runs.

Do not start code changes until baseline is recorded in a progress note.

Progress note path:

```text
notes/progress/daily/2026-06-30.md
```

Append a section:

```markdown
## Evidence VM next-speedup baseline

- branch / commit:
- existing uncommitted files:
- release binary:
- baseline nondet debug evidence-vm-run:
- baseline showcase debug evidence-vm-run:
- baseline nondet normal run:
- baseline showcase normal run:
- key counters:
```

Stop if the worktree has unrelated changes that touch inference, syntax, std semantics, or playground UI.  This task should only touch runtime / stats / debug output / design notes unless a tiny fixture is needed.

---

### Stage 1 — Add scoped direct-tail delta executor profile, no behavior change

Goal: measure whether the accepted compact signal path can be represented as a direct executable payload without materializing/resuming the old continuation tree.

Add profile-only counters:

```rust
scope_direct_tail_delta_candidates
scope_direct_tail_delta_planned
scope_direct_tail_delta_rejected
scope_direct_tail_delta_reject_not_one_shot
scope_direct_tail_delta_reject_same_handler_boundary
scope_direct_tail_delta_reject_ref_set
scope_direct_tail_delta_reject_no_materialize_fallback
scope_direct_tail_delta_reject_shape_mismatch
scope_direct_tail_delta_eval_frames
scope_direct_tail_delta_marker_ops
scope_direct_tail_delta_provider_frames
scope_direct_tail_delta_catch_foreign_boundaries
scope_direct_tail_delta_estimated_saved_then_steps
scope_direct_tail_delta_estimated_saved_marker_steps
scope_direct_tail_delta_estimated_saved_provider_steps
scope_direct_tail_delta_estimated_saved_catch_steps
scope_direct_tail_delta_shadow_mismatch
```

Build a `ScopedDirectTailDeltaCandidate` beside the current path:

```rust
struct ScopedDirectTailDeltaCandidate {
    eval_frames: SmallVec<[EvidenceEvalDeltaFramePlan; 8]>,
    marker_delta: Option<EvidenceMarkerDeltaId>,
    provider_delta: Option<EvidenceProviderDeltaId>,
    catch_foreign: SmallVec<[EvidenceCatchBoundaryDeltaPlan; 2]>,
    estimated_saved_steps: EvidenceResumeStepEstimate,
    materialize_fallback: EvidenceContinuation,
}
```

If the actual types already exist under different names, reuse them instead of adding duplicates.

Shadow conditions:

```text
- same-handler catch boundary => reject
- RefSet boundary => reject
- legacy bridge => reject
- missing materialize fallback => reject
- provider permission cert stays provider-side only
- catch foreign cert cannot provide provider permission
- shape digest must match old continuation materialization
```

Result pattern:

| Pattern | Meaning | Action |
| --- | --- | --- |
| `planned / candidates >= 80%`, mismatch 0, estimated saved steps high | direct-tail delta executor likely worth doing | Stage 2 |
| `planned` high but saved steps low | representation is possible but not hot | defer execution |
| `reject_same_handler_boundary` high | same-handler semantics blocks narrow path | keep compact signal only |
| `reject_ref_set` high | ref-set needs separate executor | stop this direction |
| `shadow_mismatch > 0` | semantic model wrong | stop and fix shadow only |
| profile traversal slows release default | profile leaked into hot path | gate behind deep profile/debug only |

Validation after Stage 1:

```bash
cargo fmt --all --check
cargo check -q -p evidence-vm -p yulang
cargo check -q --release -p evidence-vm -p yulang
cargo test -q -p evidence-vm -- --test-threads=1
cargo test -q -p yulang runtime_evidence -- --test-threads=1
tests/yulang/yulang-adversarial-corpus/probe.sh
target/release/yulang --std-root lib debug evidence-vm-run --compare-control --runtime-evidence-profile-deep bench/nondet_20_discard.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control --runtime-evidence-profile-deep examples/showcase.yu
```

---

### Stage 2 — Execute only the direct-tail signal scoped-delta path

Only start this if Stage 1 coverage is high and all mismatch counters are 0.

Gate:

```rust
const SCOPE_PLAN_DIRECT_TAIL_DELTA_EXECUTOR_ENABLED: bool = true;
```

Keep the existing compact signal executor as fallback.  Do not touch value resume yet.

Execution shape:

```text
on DirectTail signal through foreign catch scope:
  if candidate accepted:
    preserve foreign catch boundaries in carried signal payload
    attach marker/provider delta payload by ID, not by rebuilding frames
    append eval lane in compact order
    skip request-boundary profiling for accepted scope
    execute old tree only on materialize fallback
  else:
    current ScopePlanForeignCatchBoundary compact path
```

Add execution counters:

```rust
scope_direct_tail_delta_exec_hits
scope_direct_tail_delta_exec_tree_fallbacks
scope_direct_tail_delta_exec_materialized_fallbacks
scope_direct_tail_delta_exec_reject_same_handler_boundary
scope_direct_tail_delta_exec_reject_shape_mismatch
scope_direct_tail_delta_exec_saved_then_steps
scope_direct_tail_delta_exec_saved_marker_steps
scope_direct_tail_delta_exec_saved_provider_steps
scope_direct_tail_delta_exec_saved_catch_steps
```

Keep condition:

```text
- compare-control match on both representative workloads
- adversarial corpus passes
- all shadow mismatches remain 0
- scope_exec_signal_passthrough_hits stays flat or rises
- generic request signals do not rise unexpectedly
- direct-tail signals do not fall unexpectedly
- nondet improves by >= ~5% OR showcase improves by >= ~5%
- the other representative workload does not materially regress
```

Rollback condition:

```text
- any compare-control mismatch
- any catch-foreign shadow mismatch
- generic request signals rise unexpectedly
- direct-tail signals fall unexpectedly
- runtime_evidence_execute improves < 5% on both workloads while code complexity rises
- small examples regress materially
```

---

### Stage 3 — Value executor overhead investigation, still disabled by default

Do not enable `SCOPE_PLAN_FOREIGN_CATCH_VALUE_EXECUTOR_ENABLED` yet.

The earlier value executor was behaviorally clean but slower.  Treat it as an overhead problem, not as proof the semantics are impossible.

Add profile-only breakdown under deep profile or debug build:

```rust
scope_value_executor_candidates
scope_value_executor_planned
scope_value_executor_enabled_trials
scope_value_executor_eval_actions
scope_value_executor_marker_actions
scope_value_executor_provider_actions
scope_value_executor_catch_foreign_actions
scope_value_executor_materialize_fallbacks
scope_value_executor_plan_cache_hits
scope_value_executor_plan_cache_misses
scope_value_executor_allocating_materializations
scope_value_executor_direct_eval_frame_steps
scope_value_executor_legacy_delegations
scope_value_executor_reject_ref_set
scope_value_executor_reject_same_handler
scope_value_executor_reject_shape_mismatch
```

Investigate result patterns:

| Pattern | Meaning | Action |
| --- | --- | --- |
| cache misses high | plan construction overhead is the regression | precompute at frame construction or intern plan |
| direct eval actions high and slower | eval-lane dispatch too generic | specialize only hot frame kinds |
| materialize fallbacks high | executor is not actually executing | keep disabled |
| value resume hits low in representative workloads | value executor is cold | leave disabled |
| compare-control clean but wall time +20% | semantic model OK, implementation shape wrong | keep tests, disable gate |
| value executor beats legacy by >=5% with no mismatches | promote with guard | enable only accepted subset |

Validation is the same as Stage 2, but require explicit enabled/disabled same-code comparison.

---

### Stage 4 — MarkerDelta / ProviderDelta real interning pass

Only do this if Stage 1/2 shows delta IDs are on a hot accepted path.

The shadow data already suggested high reuse for marker/provider deltas, but real execution must avoid adding hash work to the hot path.

Rules:

```text
- intern at plan/candidate construction, not per resume when avoidable
- exact key only; no semantic merging of ProviderEnv scopes
- no duplicate marker scope skip
- MarkerDeltaId / ProviderDeltaId are representation handles, not permission evidence
- old continuation tree fallback remains available
```

Counters:

```rust
marker_delta_intern_calls
marker_delta_intern_hits
marker_delta_intern_misses
provider_delta_intern_calls
provider_delta_intern_hits
provider_delta_intern_misses
marker_delta_exec_hits
provider_delta_exec_hits
marker_delta_materialize_fallbacks
provider_delta_materialize_fallbacks
```

Result patterns:

| Pattern | Action |
| --- | --- |
| unique deltas low, reuse high, wall time improves | keep |
| counts improve but wall time worsens | rollback; cost moved elsewhere |
| hash/intern calls appear in normal hot path too often | move construction earlier or abort |
| provider delta exact equality has low reuse on new workload | fallback remains fine; do not broaden equality |

---

### Stage 5 — ForceValueIfThunk / known non-thunk resume cleanup

This is secondary to scoped-delta execution, but it is a good follow-up if continuation force steps remain high.

First add or reuse counters to classify `ForceValueIfThunk`:

```rust
force_value_if_thunk_steps
force_value_if_thunk_thunk_values
force_value_if_thunk_non_thunk_values
force_value_if_thunk_known_non_thunk_frame_elided
force_value_if_thunk_unknown_kept
force_value_if_thunk_effectful_kept
```

Possible safe patch:

```text
When constructing a continuation frame that immediately forces a value known by construction to be non-thunk, skip `ForceValueIfThunk` frame.
```

Do not infer non-thunk from surface syntax unless the runtime value is already known.  Thunk/value distinction is semantic.

Result patterns:

| Pattern | Action |
| --- | --- |
| non-thunk force steps high and frame elision lowers wall time | keep |
| counter drops but wall time flat | keep only if diff tiny; otherwise rollback |
| effectful thunk case changes | rollback |
| target-value-is-thunk case affected | rollback |

---

### Stage 6 — Branchless stats-off API only after structural slices

Do not begin this before Stage 2/4 unless structural work stalls.

A flag-based scatter of:

```rust
if stats_enabled { stats.foo += 1; }
```

is not acceptable as a broad hot-path change.  The only plausible design is a monomorphized stats sink:

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

struct CollectStats { stats: RuntimeEvidenceRunStats }
struct NoStats;
```

Acceptance:

```text
- fast no-stats path is branchless after inlining
- normal run without --runtime-phase-timings can use NoStats
- debug evidence-vm-run and --runtime-phase-timings keep CollectStats
- speedup >= 3% on at least one representative workload
- no readability collapse around counter sites
```

Rollback:

```text
- branchy implementation slows normal release
- speedup < 3% and diff is broad
- counter auditing becomes harder before ResumePlan work settles
```

---

### Stage 7 — Bytecode / compiled blocks later

Defer bytecode/native backend until at least one of these exists as real runtime representation:

```text
- compact ResumePlan / ScopeDelta IR
- explicit eval segment boundaries
- MarkerDeltaId / ProviderDeltaId execution or cheap materialization
- stable direct-tail scoped-delta executor
```

Otherwise bytecode just compiles the current tree-walking shape.

---

## 6. Investigation matrix

### A. Direct route / RouteCert

| Observation | Meaning | Action |
| --- | --- | --- |
| `route_cert_provider_grant_clean` high | clean provider direct path exists | consider request-free direct signal |
| `route_cert_provider_grant_dirty_add_id` high | hygiene marker state is the blocker | use guarded/scoped delta, not clean-route widening |
| `route_cert_none` high | no route evidence | leave generic fallback |
| `route_cert_static_direct` high but request-free low | static direct plumbing bug or signal bridge issue | inspect `EvidenceEffectRoute::Direct` and `request_free_yield` |
| clean route low but timings hot | route lookup is not the main target | focus continuation/scope |

### B. ScopePlan / CatchForeign executor

| Observation | Meaning | Action |
| --- | --- | --- |
| shadow mismatch > 0 | model wrong | stop before execution |
| `scope_exec_signal_passthrough_hits` high, value hits 0 | signal path is representative | optimize direct-tail signal, not value resume |
| enabled gate improves nondet but hurts showcase | keep only if showcase regression is noise; otherwise gate/rollback |
| compact tail improves same-code disabled by >=5% | keep |
| value executor regresses both | keep disabled, profile overhead |
| same-handler reject appears | fallback must remain | never pass through same-handler boundary |

### C. Marker / call boundary

| Observation | Meaning | Action |
| --- | --- | --- |
| `marker_frame_entries` high | visible cost | classify before optimizing |
| `function_call_marker_plans` high but plan cache hit high | not plan construction | focus enter/close execution |
| pure/no-active marker entries 0 | pure marker skip will not help | avoid plan-only shortcut |
| duplicate scope skip lowers count but slows wall time | cost moved | do not retry without new invariant |
| MarkerDelta unique low / reused high | interning likely useful | add real delta IDs only if hot path can consume them cheaply |

### D. ProviderEnv / ProviderDelta

| Observation | Meaning | Action |
| --- | --- | --- |
| exact same ProviderEnv compaction 0 | simple collapse false | do not implement |
| adjacent ProviderEnv different | scope order matters | no flatten |
| ProviderDelta unique low / reused high | compact delta ID likely useful | use exact keys, no semantic merging |
| nearest miss candidates appear | not invisibility | keep fallback/shadow only |
| later grant visible-compatible but slow | representation issue | do not resurrect close branch |

### E. Continuation resume / ForceValueIfThunk

| Observation | Meaning | Action |
| --- | --- | --- |
| `continuation_resume_force_steps` high | force frames hot | classify thunk/non-thunk |
| non-thunk force dominates | possible frame elision | add known-non-thunk fast path |
| `thunk_force_continuation` > 0 after fusion | regression or missed pattern | inspect forced continuation apply fusion |
| `resume_pack_thunks_forced` > 0 after fusion | regression | inspect `ForceThunk` immediate continuation apply |
| `continuation_resume_then_steps` high | tree shape still hot | scoped-delta executor likely target |

### F. Env clones / evals

| Observation | Meaning | Action |
| --- | --- | --- |
| `env_clones` high, `env_entries_cloned = 0` | cheap structural clones | do not over-optimize first |
| `env_entries_cloned` high | real clone pressure | profile frame source |
| immediate arg fast path already lowers evals | keep | add more only with exact effect-free proof |
| case literal mismatch clone still high | add only clone-before-match safe cases | no broad pattern precheck |

### G. List / data structures

| Observation | Meaning | Action |
| --- | --- | --- |
| `list_merge_calls` low/moderate | not primary | avoid broad list rewrite |
| `list_values_copied` > 0 | list flatten/copy issue | inspect list builder |
| black height cache helps but small | accepted low-risk only | do not chase as main |
| workload output formatting dominates | not VM | separate issue |

### H. Stats / profiling

| Observation | Meaning | Action |
| --- | --- | --- |
| deep profile counters nonzero in release default | bug | gate behind debug/deep profile |
| stats-off branchless gives >=3% | possibly keep | after structural slices |
| stats-off flag branches slow normal run | rollback | no branchy scatter |
| normal diagnostics become too thin | bad trade | keep core counters |

### I. Source-key / total latency

| Observation | Meaning | Action |
| --- | --- | --- |
| `collect` dominates total | source collection issue | source-key cache / static-analysis task, not VM |
| source-key hit gives `collect: 0us` | VM timing clearer | use warm cache for VM work |
| `runtime_execute` improves but total flat | cache/build overhead dominates | record separately |

---

## 7. Required validation after every kept patch

Minimum:

```bash
cargo fmt --all --check
cargo check -q -p evidence-vm -p yulang
cargo check -q --release -p evidence-vm -p yulang
cargo build -q --release -p yulang
cargo test -q -p evidence-vm -- --test-threads=1
cargo test -q -p yulang runtime_evidence -- --test-threads=1
tests/yulang/yulang-adversarial-corpus/probe.sh
```

Runtime parity:

```bash
target/release/yulang --std-root lib debug evidence-vm-run --compare-control bench/nondet_20_discard.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control examples/showcase.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control --runtime-evidence-profile-deep bench/nondet_20_discard.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control --runtime-evidence-profile-deep examples/showcase.yu
```

Normal run timings:

```bash
target/release/yulang --std-root lib --runtime-phase-timings run --print-roots bench/nondet_20_discard.yu
target/release/yulang --std-root lib --runtime-phase-timings run --print-roots examples/showcase.yu
target/release/yulang --std-root lib --runtime-phase-timings run --print-roots examples/03_for_last.yu
target/release/yulang --std-root lib --runtime-phase-timings run --print-roots examples/02_refs.yu
```

Full gate, when the slice is ready:

```bash
YULANG_PERF_GATE_REPEAT=3 scripts/performance-gate.sh
```

---

## 8. Patch acceptance rubric

Keep a patch only if all required semantic checks pass and at least one is true:

```text
- nondet median runtime improves by >= 5%
- showcase median runtime improves by >= 5%
- a structural counter is eliminated without wall-time regression and the diff is clearly preparatory
- a previously expensive debug/deep profile traversal is removed from release default
```

Reject or disable a patch if:

```text
- compare-control mismatches
- adversarial corpus fails
- any shadow mismatch becomes nonzero
- generic request behavior changes unexpectedly
- direct-tail signals drop unexpectedly
- generic request signals rise unexpectedly
- wall time worsens on both representative workloads
- complexity rises without a clear next execution slice
```
