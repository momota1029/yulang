# dots cycle147 — recovery and partial general bridges

Started 2026-11-12T18:26:34Z. Environment/worker restart interrupted this cycle. Recovery began 18:57 UTC; no old Lean/lake writer remained. The source files and caches survived. Recovered 10 new modules, committed locally as 9359caf42; publication is this report's commit on work/dots-main.

## Fresh state / constraints
Integration 6cff680cc, I-25 ACTIVE. Prior146 completed. Repository instructions re-read; frozen Audit.lean and README unchanged. No general target/semantic definition was changed. Only work/dots-main is published. Full local build and Yulang2 execution were not performed; existing definitions and regression sources were used for comparison, not new Yulang2 behavior claims.

## Results (all auxiliary/soundness components, not the complete theorem)
1. For arbitrary reachable support states and a selected recorded key, ordinary Extension of its historical context preserves the emitted child list; historical graph edges then prove Generated for those children without Joint. A weaker finite source-ID binding equality certificate permits carrier/view changes as well. Terminal and covered selections are discharged, leaving UncoveredBindingsJoint explicit. This is a conditional GeneratedChildren composition, not an unconditional V5 bridge.
2. Certified point reobservation can change emitted bindings. A modeled reachable regression has a new emitted child which is not in the historical Generated set. Stability is NOT asserted, so this is not a V5 counterexample.
3. For arbitrary actually recorded nominal heads with finitely many distinct input binder names and type bounds, compute inspection/capture/projection exactly in the same original model. The repeated-name two-position case has an iff with explicit SameParameters, allocation merge equations and generated materialization residuals. Those residuals are not proved universally.
4. For a checked terminal declaration with one associated nominal request targeting the already constrained head source, finite distinct names, the specified query/descriptor shape and original Models, derive BranchModels without assuming BranchModels. This does not cover arbitrary output identities or arbitrary declarations.
5. For an inhabited real support trace that loses all models, locate a model-destroying merge. A single historical packet covering both sites prevents this loss. Existence of an inhabited model for all reachable states is not assumed or proved.

## Remaining
General V5 remains 6/14 supplied, 8/14 unresolved. In particular SameModelBranchAtSelected and the residual for uncovered/binding-changing selections remain open. These results do not provide a total executor, full finite diagnostics, arbitrary canonical order, or full language correctness.
Next: derive same-model repeated-name merge/materialization residuals from actual stable selection; handle binding-changing selected children without assuming historical coverage; connect the constrained-source terminal branch result to unrestricted associated outputs.

## Verification
Recovered focused build: 746 jobs, exit0. Audit/Cycle147.lean: 57 unique public theorems, trust=0 exit0, standard propext/Classical.choice/Quot.sound only. Full-module scoped gate: 121 declarations, exit0. Exact type output: 57 entries, exit0. The public helper schemas_exact had been omitted from the interrupted audit shard; it was added and the audit rerun. No proof was admitted.
Independent read-only review performed on recovered sources. Full local build was deliberately not run. CI is not claimed here.

## Recovery / failures
Remote heartbeat last updated 18:36, then worker/environment disappeared. Heartbeats due after that time and 30-minute source publication were missed. Recovery verified no old writer and revalidated all retained sources rather than claiming interrupted commands finished. No source had been published before recovery; only the start/progress heartbeat. Source publication now contains the complete recovered source changes, audit, type list, report and completed heartbeat. No repeated blob approval request was made.

## Verification output (exact diff-gate output)
```
verify-lean: . @ 9359caf42 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalCompletion.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalView.lean only appended (plus top import lines)
ok: lean/Audit/AstraConfluence.lean only appended (plus top import lines)
ok: lean/Audit/AstraOrder.lean only appended (plus top import lines)
ok: lean/Audit/Cycle136.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Finished.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Followup.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Formation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Joint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Refresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Terminal.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Tree.lean only appended (plus top import lines)
ok: lean/Audit/Cycle139.lean only appended (plus top import lines)
ok: lean/Audit/Cycle139Followup.lean only appended (plus top import lines)
ok: lean/Audit/Cycle140.lean only appended (plus top import lines)
ok: lean/Audit/Cycle141.lean only appended (plus top import lines)
ok: lean/Audit/Cycle141Recorded.lean only appended (plus top import lines)
ok: lean/Audit/Cycle142.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupport.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

The complete theorem signatures and audit output are in dots-cycle-147-validation.md.
