# Cycle229 — failed exact-empty counterexample and optional-output successor

Started 2026-11-17 01:30 UTC; research cutoff02:15; hard deadline02:25.
The latest user direction is55minutes, overriding I43's older25minutes.
Integration/inbox re-read at02:07: a3251d569, through I43, no new STOP.

## Recovery of228

The prior running heartbeat and lack of a final report indicated interruption.
No overlapping prior process was observed on recovery. Surviving committed
files matched c963b1e9. One untracked verified V8Extreme wrapper was preserved,
audited and published with a reconstructed228report and crash note at
01863ee3fbb667a2f46b27555da7f7ecf21abb0a. The228ownership/probe audits were rerun
(116+279constants), and the recovered wrapper's1constant audited independently.
This is recovery, not a claim that228met its original deadline.

## What was proved

All new results concern the actual V8 boundary; no semantics or guards changed.

1. `GeneralDictionaryJournalRefinement229Refresh.certificate`, `step`,
   `not_stable`: the original228stage admits a real trusted exactEmpty-head
   refresh at source4, so it is not stable.
2. `GeneralDictionaryJournalRefinement229Diagnostic.regression`: that refreshed
   state is reachable, has a full journal model, and is actually V8 rejected.
   `Raw.no_head_model` quantifies every raw model of the refreshed snapshot and
   excludes current HeadModels, not just the chosen old model.
3. `GeneralDictionaryJournalRefinement229Selected.selected`: before the refresh
   the actual V8 local diagnostic is selected.
   `Regression.selected_without_instance` combines reachability, a surviving
   journal model, selection, no current Instance, and non-stability.
4. `Regression.stage_evidenceAt`: the ORIGINAL B4SkeletonV8.EvidenceAt at this
   exact stage holds vacuously because the only generated demand is not stable.
   This rules out presenting the weaker obstruction as an EvidenceNode refutation.
5. `GeneralDictionaryOptionalOutput229.no_test`: for EVERY normalized Test,
   the optional-field value `exactEmpty | record(0,width,exactEmpty)` has no exact
   head. It is below width, unequal to width and bottom. `Expression.compiled`
   and `pattern_value` verify existing syntax and compiler semantics.
6. `GeneralDictionaryOptionalRegression229.selected_without_instance`: a new
   checked declaration with that output has an actual initial/install/reobserve
   V8 path, full journal model and V8 selected diagnostic, but no current total
   Instance for that model. This is NOT yet the original EvidenceNode target.
7. `output_refresh_barrier`: for EVERY candidate context and certified Refresh
   from the optional stage, neither source4 nor the retained lower aggregate can
   become Known. The generic `Expression.no_refresh_known` derives this from
   a concrete preserved optional-valued model, not an assumed stability premise.

## Acceptance and remaining obligations

I41.4 EvidenceNode remains OPEN. ProtectedOverlap remains OPEN.
The exact-empty candidate is conclusively non-stable. The optional candidate
blocks that particular completion but does not exhaust all administrative
updates, especially generated identities. No full counterexample or boundary
change is claimed. No question requiring a new language design choice was
established, so no design-choice question was invented.

Next steps (in order):
- Complete observations for the optional fixture's generated upper/actual
  identities using trusted inputs, with preserved support and no new assumptions.
- Exhaust equate/reobserve/enqueue/merge/install/refresh before claiming Stable.
- Test exact EvidenceAt including its dictionary premises; replay/materialization
  still needs a proof or an actual stable counterexample, not another weakened goal.

## Verification and publication

Focused `lake build <module> --wfail` only, using cached dependencies.
`lake env lean --trust=0` independent module audits allow only propext,
Classical.choice,Quot.sound. No sorry/new axiom/native_decide.
No full `lake build`, verify-lean.sh, remote CI, or Yulang2 runtime result claimed.
`lean/Audit.lean` and `lean/README.md` byte-match integration; barrel imports append.

Verified checkpoints:
- f34b805d3e90dd17c884f5d657a59827815d78d9: refresh/raw/diagnostic4modules65constants.
- b7be5a0f6dd6a29a83def05bf839a1f608a7a5f3: selection/stability guard4modules77constants.
- 2490add2d337c69bfe383faaf894f77673b5ea1f: optional fixture15modules251constants.

Final verification, elapsed time and file inventory are appended below.
Usage budget: unknown. All source publication is confined to work/dots-main.

## Final research additions

- `GeneralDictionaryOptionalJoint229.lower_output`: for every model satisfying
  the optional stage's full journal, its retained lower aggregate is equivalent
  to the optional output value.
- `no_current_packet`: for every such model, the current plan's complete packet
  is false. `no_install`: for every proposed effect whose occurrence is root,
  actual Installable at this stage is impossible. This strengthens the
  single-model obstruction without changing the target.
- `GeneralDictionaryOptionalOpenRefresh229` examines why the remaining gap is
  not cosmetic: generated upper identities are not known by the five-slot
  snapshot, while the old input supports their exact width head. A new snapshot
  with that head still requires a complete certified construction; an exact
  value in one full model is not substituted for trusted evidence.

## Lean source inventory (25 modules)

- `lean/Yulang/GeneralDictionaryOptionalCurrent229.lean`
- `lean/Yulang/GeneralDictionaryOptionalCycles229.lean`
- `lean/Yulang/GeneralDictionaryOptionalEnable229.lean`
- `lean/Yulang/GeneralDictionaryOptionalExpression229.lean`
- `lean/Yulang/GeneralDictionaryOptionalInitial229.lean`
- `lean/Yulang/GeneralDictionaryOptionalInstall229.lean`
- `lean/Yulang/GeneralDictionaryOptionalJoint229.lean`
- `lean/Yulang/GeneralDictionaryOptionalOpenRefresh229.lean`
- `lean/Yulang/GeneralDictionaryOptionalOutput229.lean`
- `lean/Yulang/GeneralDictionaryOptionalRaw229.lean`
- `lean/Yulang/GeneralDictionaryOptionalRawStage229.lean`
- `lean/Yulang/GeneralDictionaryOptionalReachable229.lean`
- `lean/Yulang/GeneralDictionaryOptionalRegression229.lean`
- `lean/Yulang/GeneralDictionaryOptionalSelected229.lean`
- `lean/Yulang/GeneralDictionaryOptionalSource229.lean`
- `lean/Yulang/GeneralDictionaryOptionalStage229.lean`
- `lean/Yulang/GeneralDictionaryOptionalStageSafety229.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229Cycles.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229Diagnostic.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229Raw.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229Refresh.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229Regression.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229Selected.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229Snapshot.lean`
- `lean/Yulang/GeneralDictionaryJournalRefinement229StageSafety.lean`

## Verification limitations encountered at close

A combined25-module independent audit reached its240second limit without a
completion result. A conditional exact-target wrapper was attempted late in
the cycle; its focused build reached120seconds, then90seconds after reducing
imports, without completion. It is excluded from the published Lean tree and
barrel. No theorem or audit PASS is claimed for that wrapper. Existing23module
checkpoint audits remain valid. The two final additions are checked separately.
