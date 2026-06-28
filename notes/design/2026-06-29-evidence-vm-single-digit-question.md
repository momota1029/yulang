# Evidence VM single-digit runtime question

This note is a question sheet for the next Evidence VM performance review.
The goal is not to ask for another local micro-optimization. The goal is to
identify the next structural change that can make `bench/nondet_20_discard.yu`
stable in the single-digit millisecond range without weakening handler hygiene.

## Goal

Target:

- `bench/nondet_20_discard.yu`
- release `runtime_evidence_execute`
- stable single-digit milliseconds
- `--compare-control` must keep matching the Control VM

Current measurements after commit `2a56d22a`:

- `bench/nondet_20_discard.yu --compare-control`
  - roughly `10.5ms` to `12.1ms`
  - `compare.control: match`
- `examples/showcase.yu --compare-control`
  - roughly `24ms` to `26ms`
  - `compare.control: match`

The historical target is that an earlier Control VM path reached about `7ms`
on the 20x20 nondet workload. The Evidence VM has much better semantic
structure, but it is not yet clearly faster in this workload.

## Current runtime shape

The Evidence VM is no longer just the old request/marker runtime with a few
extra tables. It now has a permission-native close path for several proven
direct-tail cases.

Accepted native close branches:

- `NativeProviderPair`
- `NativeProviderPrefixBoundary`
- `NativeProviderEnvForeignBoundary`

These branches are documented in:

- `notes/design/evidence-vm-native-close-invariants.md`

They are deliberately narrow. In particular:

- `NativeProviderPrefixBoundary` is a prefix-boundary permission exposure, not a
  handler-id equality rule.
- `NativeProviderEnvForeignBoundary` covers only the nearest-ProviderEnv grant
  branch.
- nearest ProviderEnv miss is not evidence of invisibility.
- later ProviderEnv grant matched visible behavior in shadow runs, but the
  native-close attempt was slower, so it remains profile-only.

Rejected later-grant deep traversal is now gated behind debug builds or the
explicit `--runtime-evidence-profile-deep` flag. Release default does not walk
the continuation tree just to inspect this rejected path.

## Current hot observations

Representative nondet counters from the recent profiles:

- `expr_evals: 48288`
- `env_clones: 37428`
- `apply_value_calls: 17481`
- `primitive_apply_calls: 2123`
- `thunk_forces: 6469`
- `thunk_force_expr: 3046`
- `thunk_force_continuation: 840`
- `continuation_resume_steps: 21566`
- `continuation_resume_force_steps: 11781`
- `marker_frame_entries: 13526`
- `marker_frame_scoped_apply_entries: 4032`
- `marker_frame_marked_apply_entries: 3067`
- `marker_frame_continuation_resume_entries: 1680`
- `marker_frame_marked_force_entries: 3024`
- `provider_env_values: 462`
- `provider_env_route_lookups: 861`
- `provider_env_route_hits: 462`
- `function_call_marker_plans: 11448`
- `list_merge_calls: 420`

Deep marker profile:

- `marker_frame_markers: 41697`
- `marker_frame_add_id_markers: 27371`
- `marker_frame_active_add_id_markers: 24808`
- `marker_frame_frame_only_entries: 0`
- `marker_frame_no_active_add_id_no_handler_entries: 0`
- `active_marker_plan_pushes: 7293`
- `active_marker_plan_dedupes: 6233`

ProviderEnv / Then compaction profile:

- release default:
  - no rejected later-grant traversal
  - no compaction traversal
- deep profile `bench/nondet_20_discard.yu`:
  - `provider_env_then_compaction_candidates: 1722`
  - `provider_env_then_compaction_adjacent_provider_env: 441`
  - `provider_env_then_compaction_same_provider_env: 0`
  - `provider_env_then_compaction_provider_env_identity_tail: 0`
  - `provider_env_then_compaction_provider_env_then_first: 861`
  - `provider_env_then_compaction_provider_env_then_second: 0`
  - `provider_env_then_compaction_nested_same_env: 0`
  - `provider_env_then_compaction_nested_different_env: 441`
  - `provider_env_then_compaction_reject_different_provider_env: 441`
  - `provider_env_then_compaction_reject_marker_frame_between: 420`
  - `provider_env_then_compaction_reject_request_boundary: 1260`
- deep profile `examples/showcase.yu`:
  - `provider_env_then_compaction_candidates: 3532`
  - `provider_env_then_compaction_adjacent_provider_env: 951`
  - `provider_env_then_compaction_same_provider_env: 0`
  - `provider_env_then_compaction_provider_env_identity_tail: 0`
  - `provider_env_then_compaction_provider_env_then_first: 1766`
  - `provider_env_then_compaction_provider_env_then_second: 0`
  - `provider_env_then_compaction_nested_same_env: 0`
  - `provider_env_then_compaction_nested_different_env: 951`
  - `provider_env_then_compaction_reject_different_provider_env: 951`
  - `provider_env_then_compaction_reject_marker_frame_between: 815`
  - `provider_env_then_compaction_reject_request_boundary: 2445`

Reading so far:

- exact same ProviderEnv collapse does not appear in the representative
  workloads.
- adjacent ProviderEnv frames exist, but the observed adjacent frames carry
  different environments.
- simple `ProviderEnv(env, ProviderEnv(env, k)) => ProviderEnv(env, k)` is not
  the next useful optimization.
- simple duplicate marker scope skipping reduced marker frame entries but made
  runtime slower.
- the remaining cost likely sits in the representation and execution of
  `MarkerFrame` / `ProviderEnv` / `Then`, not in a single missing hash-table or
  allocation tweak.

## Changes that helped

Accepted changes in the latest tuning pass:

- `PrimitiveArgs = SmallVec<[SharedValue; 4]>`
- dense effect-call route table indexed by apply expression
- dense operation visibility table indexed by apply expression
- dense provider lookup table for provider-route call sites
- `SmallVec` for provider env refs/views and small provider lookup internals
- avoid cloning provider env in `with_provider_env` by reusing the popped active
  frame's environment for close
- gate detailed runtime breakdown stats while preserving core counters
- preserve shared-continuation append only when the frame is not a scope
  boundary
- fast path for `eval_expr_result` via direct runtime expression indexing
- avoid repeated path sharing in force-effect call path

These changes improved the baseline, but not enough to make the runtime
stable in the single-digit range.

## Changes that did not help

Rejected or reverted attempts:

- removing the main runtime stats counters from release default
  - little speed impact and worse diagnostics
- thread-local shared `Rc` for `Bool` / `Unit`
  - slower than allocating the small values normally
- frame-less close for `MarkedApply`
  - representative workloads did not hit it
- duplicate marker scope skip
  - reduced `marker_frame_entries` from about `13526` to `7293`, but runtime
    got slower because the cover checks and resulting close shape cost more
- `Tuple` / `DataConstructor` payload `SmallVec`
  - too much diff for noise-level benefit
- fat LTO / `target-cpu=native`
  - occasional `9.7ms`, but average remained around 10ms and build cost was too
    high to count as the language-level solution
- later ProviderEnv grant native close
  - visibility matched legacy behavior, but the native-close path was slower
  - kept as profile-only behind `--runtime-evidence-profile-deep`
- exact same ProviderEnv compaction
  - no exact same-env candidate in nondet/showcase

## Constraints

Any proposed optimization must preserve:

- `--compare-control` result equality
- `tests/yulang/yulang-adversarial-corpus/probe.sh`
- existing native close invariants
- separation between:
  - `NativeProviderPrefixBoundary`
  - nearest ProviderEnv grant
  - nearest ProviderEnv miss
  - later ProviderEnv grant

Do not propose:

- widening native close branches without a shadow phase and an explicit cert
- treating nearest ProviderEnv miss as invisibility
- using arbitrary `any ProviderEnv` presence as permission evidence
- flattening `Then` / `ProviderEnv` across dynamic scope boundaries without a
  scope-preserving invariant
- path/name/test-specific branches
- weakening marker hygiene or provider permission visibility

## Questions

1. What is the next structural optimization most likely to make
   `bench/nondet_20_discard.yu` stable below `10ms`?

2. Is the current Evidence VM still too close to a request/marker/continuation
   machine? If so, what is the smallest representation change that would move
   it toward a real Koka-style evidence-passing runtime?

3. Should `MarkerFrame` / `ProviderEnv` / `Then` be replaced by a different
   continuation representation, such as:
   - a scope-indexed segment stack
   - a deque-like continuation spine
   - compiled bytecode blocks with explicit scope opcodes
   - a provider-permission state threaded through direct-tail handlers

4. Can permission-native marker semantics avoid dynamic marker frame push/pop
   for the nondet workload without reintroducing the old rejection-list hygiene
   model?

5. Is there a safe way to fuse the common nondet pattern:

   ```text
   branch(), k -> loop(loop xs k(true), k(false))
   ```

   so that `k true` / `k false` do not repeatedly rebuild the same marker and
   provider continuation shape?

6. Should the lowering / mono stage emit a more specialized runtime evidence
   surface, rather than asking the runtime VM to rediscover handler/provider
   shape dynamically?

7. Are the remaining `env_clones`, `thunk_forces`, and continuation resume steps
   symptoms of one missing representation, or are they separate costs that
   should be attacked independently?

8. If profiler access is available, which functions or events should be measured
   first to distinguish:
   - continuation representation cost
   - marker close cost
   - provider environment restoration cost
   - closure environment cloning cost
   - list construction / merge cost

9. Is `std.control.nondet.list` itself forcing a pathological allocation shape?
   If yes, what accumulator or builder design could preserve result order and
   handler semantics while reducing runtime pressure?

10. What changes are likely to look promising but break hygiene or merely move
    cost elsewhere?

## Desired answer shape

Please rank possible next directions by:

- expected speedup
- semantic risk
- implementation size
- ability to validate through shadow stats and `compare-control`

For each promising direction, include:

- the invariant that would make it sound
- which counters should move if the direction is right
- what the first small patch should measure
- what would falsify the direction

Also include a short "do not do next" list.
