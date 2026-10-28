# NATIVE-IDLE-CHILD-LAUNCH/r5 independent review

## Verdict

**REJECT.** Under R5 contract lines 152–155, this closes the sprint incomplete; no revision or bounded checks are authorized.

The review was performed by `/root/native_idle_child_launch_r5_review` (`compiler_referee`, requested Sol/medium; observed model/effort UNKNOWN). It inspected source and governing definitions before producer explanations. The reviewer was read-only; this receipt is persisted by the primary from its returned findings.

## Blocking findings

1. **Rust use-after-move.** In the isolated `candidate_scheme.rs:8022`, `identity: ScopeTransformer` is moved into `test_replace_scope_transformer`; line 8028 then uses `Some(identity)`. `ScopeTransformer` in `candidate_scope.rs:30` is neither `Copy` nor `Clone`, and the helper in `candidate_context.rs:1978` takes ownership. This statically identified likely E0382; no compiler ran. A future packet must authorize a valid ownership arrangement and focused compilation.

2. **Completed authentication does not reread the physical slot.** `fresh_use_fiber_emission` (`candidate_context.rs:1864`) checks retained admission/emission records and their saved readback. The physical read only occurs during construction in `candidate_extrusion.rs:857`, via `candidate_physical_slot_bound` at line 648. The return recorder at `candidate_context.rs:1950` and the completed predicate do not consult the current vector. Replacing/removing the addressed `bounds[row].direct_upper_rows[index]` or matching atom/effect lane while retaining evidence leaves authentication unchanged. This violates the contract’s current-state physical-slot requirement (lines 123–125).

3. **Restoration invocation association is recorded but not authenticated.** `RestorationReturnObservation` (`candidate_context.rs:167`) carries a restoration handle, but `candidate_scheme.rs:7799` does not check it, and `authenticate_demand_transport_observed` at line 901 does not consume return observations. Replacing the handle with a sibling while keeping emission, cause and readback leaves matching/authentication unchanged. There is no independent invocation identity plus begin-to-return join, contrary to contract lines 121–125 and 133–135.

4. **Context changes exceed Amendment 01.** The amendment permits one test helper to replace a raw transformer row and return the previous value. The submitted `candidate_context.rs` also adds `RestorationReturnObservation` (line 165), a State vector (line 991), and observer recorder/accessor methods (lines 1945–1959). No retrospective waiver is granted.

5. **Mutation assertion runs before restoration.** In `candidate_scheme.rs:8024`, rejection is asserted while the raw transformer is replaced; restoration occurs at line 8028. If the assertion fails, the original row is not restored. Contract lines 131–133 require restoring before asserting.

## Proof and bounded evidence

The Lean artifact is honestly incomplete: `NativeIdleChildLaunchR5.lean:7` stops before the capacity-growth observer. `appendFrame_exact` (line 149) and `writeRunning_exact` (line 194) are separate local calculations. They do not compose successful Idle/Some launch through resource observation, seeding, enqueue, processing/diagnostic writes or receipt publication. The first missing owner is `candidate_prepare_replay_wait` in the submitted `candidate_context.rs:4116`, including capacity observation at lines 4121–4127. All eleven declarations are unchecked; type printing and complete axiom audits are NOT_RUN.

The original `SourceProblem.InferenceSoundness` quantification remains unchanged:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The separate `NativeCorrespondence` obligation remains open. No concrete parent instance or shared source witness follows from these local calculations.

The recorder is structurally reachable at the ordinary successful restoration return (`candidate_extrusion.rs:1023–1028`). FreshUse distinguishes source and destination bounds and checks the mapped relation against the destination. Existing ancestry authentication resolves raw transformer contents (`candidate_context.rs:3035–3040`), so same-ID mutation is a meaningful falsifier once the ownership and authentication gaps are repaired. Fixture nonemptiness and execution are unverified.

## Deviation

The Rust worker disclosed two prohibited, read-only Git commands: `git diff --stat` and `git diff --check`. No mutation was reported; this review did not independently authenticate execution history. The commands remain a contract deviation and are not waived. The findings above independently require rejection.

## Frozen artifact hashes

```text
Contract dacdb0dac5b36b13d3e1ee3b8ea37d08195668b4e4620a5fba5d7fdd6ca33ecf
Amendment 01 1f75d1fde7945f7bb937daf26201ca6cb9ffd708182d24186e9fef5b86170687
Amendment 02 b8be576a1890081f7aa0f8be759e7922941d255a7b1da31ed89a74b1a592c787
candidate_scheme.rs 6164824155f75c9c164d40b6a7c6dc2ebf9de12c10ff23bb0086e5044b0f0142
candidate_extrusion.rs e885c26fb77aa7619cb05c40148b841b5ed5d6e7111dea8f8299294c9b0ba0e0
candidate_context.rs 6e6259e1ed0d612a0e219abc6f86211299c4d2c7ec124566f459b29a9526d1c2
NativeIdleChildLaunchR5.lean 282e0f68922d3176e0d98aab04e535426cf2558403f2648ee4916ec5bb1644f4
proof handoff 1757aed4b4a6bf0657596f3a826845a0fd550078573073ed128c670d3b8620a8
Rust handoff a3c39846a6ebff047bcf327c347717758bdffe1f969dee2d50b9250207920809
```

Review activity was read-only and used source inspection and hashing only: no checks, Git, builds, tests, Lean/Lake, formatter, descendants or background processes. The authenticated clock interval was 09:12:30–09:14:11 UTC; total assignment duration was not measured. No files were written by the reviewer; the reviewer is STOPPED with no owned writers or generated artifacts.
