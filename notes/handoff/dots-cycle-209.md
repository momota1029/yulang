# dots cycle209 — semantic reinspection and current-frame evidence

Start: 2026-11-15T09:30:00Z (scheduled wake; execution began approximately09:35).
Proof/research and independent review continued through10:14UTC, after a first checkpoint.
Final verification/publication window:10:15–10:25UTC. Hard deadline10:25UTC.
Publication target: `work/dots-main` only. No writes to integration/main.

## Result

17 new Lean modules,102 theorem declarations. **Unrestricted EvidenceNode and
FreshCompletion remain open.** This is a verified checkpoint, not completion of B4.

Main advance: a stored parent's current certificate can be reconstructed without
assuming equal input-center names or a preexisting current certificate. The final
`SemanticReplay209.nominal_certificate` derives declaration/report agreement from
checked key matching plus a descriptor-preserving refinement and the old successful
nominal/variable head trace. It transports total packet/head-schema meaning and all
current alias-class output bodies semantically. Explicit/default output terms are
total and unrestricted; the head/refinement/point restrictions below are not hidden.

### Exact scope of the strongest replay

For all roles, checked compiled registry values, corrected-boundary reachable state,
root/focus/key, current Frame, historical stored plan at the same focus and key:
if the focus has point arguments, historical→current context has `Refines`, every
old head query has `FinishedObservation197.Syntax` (variables/nominals only), and a
fixed assignment models the current journal, then `SemanticReplay209.nominal_certificate`
constructs `TotalEvidence206.Certificate` at that current Frame in that same assignment.
Given ordered evidence for its children, `nominal_evidence_node` assembles the node.
No exact-center equality, assumed current packet validity, report equality,
constructor injectivity, altered Evidence, or new model witness is a premise.

`CollapsedCenters209.nominal_certificate` weakens the point premise to semantic
equivalence of each input interval's endpoints in the **specified model**. This is
still a real restriction; it is not asserted for arbitrary intervals or all models.
`SemanticReplay209.nominal_generated_children` obtains recorded child generation
without model existence or point arguments under its stored-parent/refinement/head
conditions. The genuinely fresh parent case remains the named FreshCompletion gap.

### Other results and classification

- Frame209 / Readback209: exact ordered children independent of current Frame and
  witness model; unique source readback of an erased payload; exact node inversion.
  AnyModelInstance is only a comparison relation, not replacement language Evidence.
- Expression209 / BodyTransport209: auxiliary congruence for all total expression
  constructors (including invariant nominal arguments, records, variants, unions),
  and explicit/default body meaning under semantic environment agreement.
- Configuration209 / Observed209 / Reinspection209: auxiliary persistent data and
  earlier restricted replay; the final SemanticReplay result removes their stronger
  exact-input premise rather than claiming those assumptions hold globally.
- PointTransport209 / OutputBridge209: actual stored default outputs extend to the
  whole current alias class, even after reobservation, under point input semantics.
  `default_certificate` explicitly still requires current packet semantics.
- HeadTransport209: all-query actual-head-schema transport, including scalar and
  structural queries; semantic roots/binders are sufficient, no report premise.
  Deferred schema transport does not manufacture a completeness/unknown=false proof.
- FrameSemantics209 / CurrentCertificate209: current-frame binder and body agreement;
  existing certificates can use any current Frame at a point focus in the same model.
  `node_iff` fixes that frame and exact ordered child evidence. This is representative
  independence, **not evidence existence from selected/stable**.
- TransportExamples209: distinct names1/2 with point inputs; negative interval
  [bottom,Int] whose valid centers yield different positional defaults.
- ReplayExamples209: whole total-packet recentering with a scalar head and distinct
  centers; does not pretend those fixture plans are recorded/current Frames.
- CollapsedExamples209: syntactically nonpoint endpoints that denote equal values
  support semantic transport, complementing the negative noncollapsed interval.

Exact Lean quantified types of all102 declarations are recorded in
`notes/design/2026-11-15-cycle209-declarations.md`. Their classes above distinguish
auxiliary lemmas, restricted-fragment soundness, and concrete regressions.

## Remaining work / no target weakening

1. General improving reobservation can change descriptor/report captures and is not
   necessarily `Refines`. The report-preserving nominal route cannot be reused there.
2. For noncollapsed intervals, input-center agreement fails without additional
   semantic information. The negative fixture concerns this lemma only; it is not
   a reachable-state counterexample to the assigned EvidenceNode.
3. A fresh selected parent may have no historical packet witness. The named
   FreshCompletion obligation is not proved. Do not revive the refuted general
   HeadBaseline assumption for already-recorded parents without journal models.
4. Global EvidenceNode must cover the exact I38 selected domain. None of the
   restricted theorem types substitutes for that assignment. No new target
   refutation, STOP, or model-changing repair was established.

## Recovery, instructions and concurrency

Previous208 heartbeat was completed and its report existed; no recovery cycle was
needed. Fresh integration/orders/inbox reads preceded research. Initial integration
was54a61421b5942eaef3eb54508571cc335b3430e2; latest fetched and merged integration is
c461ff2bf5ca3794081de9f05ab92b2e899ef3ae. Inbox remains I38 with SHA
6058b44ec4a123db6875e66f71b06663f12993e6 (fresh read near10:11UTC); no STOP.
Merge conflicts consisted of newer208 completion documents/heartbeat and append-only
209 imports/index versus older integration copies; the newer completed208 material
and all additions were preserved. No existing Lean lines removed. Historical208
rank module/audit on work/dots-main were preserved, not counted as209 work.

One delegated reviewer implemented separate new regression/head-transport files
and independently checked replay/certificate scope. No overlapping file writers.
Focused Lean jobs used LEAN_NUM_THREADS=1. Other repository tasks were independent.
Heartbeat publications at09:36,09:40,09:51,09:58,10:08; final heartbeat records outcome.
The09:50 heartbeat was delayed about1min by checkpoint publication; no long idle gap.

## Verification

- Focused `lake build --wfail` over the17 named209 modules: exit0,1329 cached/dependency
  jobs counted. This was **not** an umbrella/full build; only named targets were built.
- `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle209Reinspection.lean`: exit0,
  36 declarations. `Audit/Cycle209SemanticReplay.lean`: exit0,66 declarations.
- All102 printed axiom sets contain only propext/Classical.choice/Quot.sound.
- Independent direct lean invocation for the second audit also exit0.
- Exact declaration-type emission: exit0. An initial temporary diagnostic used an
  unavailable pp.width option; it was removed and rerun successfully. No repository
  proof depended on it. Initial elaboration/linter failures were corrected before
  final strict build/audit; no unverified proof files were published.
- `bash tools/verify-lean.sh . c461ff2bf5ca3794081de9f05ab92b2e899ef3ae --no-build`:
  exit0. Full output below; this gate is explicitly **diff checks only, NO build**.
- Full repository build, all old audits and supervisor-wide AxiomGate were not run,
  per standing orders. Supervisor must perform them after fetching the publication.
- Existing Yulang2 audit/oracle material was inspected for context. No new live
  Yulang2 execution was performed; these are Lean semantic/representation results,
  not a new executable behavior claim. No language-spec decisions were changed.
- Usage quota: unknown.

## Publication and next resume

First checkpoint6375f6e2963730a4db1278a666766a0df1e7ef6e was published and all10 files
read back with matching blobSHAs. Final publication uses a fresh branch lease and
exact file readback; final commit and completion time are reported in chat and the
canonical heartbeat. Local final proof commit8d350eeb0; all new code is imported by
append-only umbrella imports and audited in two new parts. Old large Audit/README
were not edited. Resume at the three semantic gaps above; preserve all209 results.

## Full diff-only gate output

```text
verify-lean: . @ 8d350eeb0 (base c461ff2bf5ca3794081de9f05ab92b2e899ef3ae)
ok: no removed lines in lean/ since c461ff2bf5ca3794081de9f05ab92b2e899ef3ae
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/ActualBoundaryAgreement.lean only appended (plus top import lines)
ok: lean/Audit/ActualBoundaryHolePhases.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalCompletion.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalView.lean only appended (plus top import lines)
ok: lean/Audit/AstraConfluence.lean only appended (plus top import lines)
ok: lean/Audit/AstraOrder.lean only appended (plus top import lines)
ok: lean/Audit/AuditFrame179.lean only appended (plus top import lines)
ok: lean/Audit/AuditNested179.lean only appended (plus top import lines)
ok: lean/Audit/AuditNestedLimit179.lean only appended (plus top import lines)
ok: lean/Audit/AuditRawFrame179.lean only appended (plus top import lines)
ok: lean/Audit/CanonicalHoleTransport.lean only appended (plus top import lines)
ok: lean/Audit/CenteredAdministrativeComposition.lean only appended (plus top import lines)
ok: lean/Audit/CenteredBoundary.lean only appended (plus top import lines)
ok: lean/Audit/CenteredCanonicalExecutor.lean only appended (plus top import lines)
ok: lean/Audit/CenteredCompletionRegistered.lean only appended (plus top import lines)
ok: lean/Audit/CenteredDirectAccessibility.lean only appended (plus top import lines)
ok: lean/Audit/CenteredFixedChoice.lean only appended (plus top import lines)
ok: lean/Audit/CenteredGroundComposition.lean only appended (plus top import lines)
ok: lean/Audit/CenteredNonterminalInstall.lean only appended (plus top import lines)
ok: lean/Audit/CenteredPermutationSimulation.lean only appended (plus top import lines)
ok: lean/Audit/CenteredPointBridges.lean only appended (plus top import lines)
ok: lean/Audit/CenteredReachablePermutation.lean only appended (plus top import lines)
ok: lean/Audit/CenteredSourceContinuation.lean only appended (plus top import lines)
ok: lean/Audit/CenteredSourceInvariant.lean only appended (plus top import lines)
ok: lean/Audit/CenteredSourceLiveRetention.lean only appended (plus top import lines)
ok: lean/Audit/CenteredSourceSnapshotLedger.lean only appended (plus top import lines)
ok: lean/Audit/CenteredSourceUnsettledRefresh.lean only appended (plus top import lines)
ok: lean/Audit/CenteredTerminalProduction.lean only appended (plus top import lines)
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
ok: lean/Audit/Cycle143.lean only appended (plus top import lines)
ok: lean/Audit/Cycle144.lean only appended (plus top import lines)
ok: lean/Audit/Cycle145.lean only appended (plus top import lines)
ok: lean/Audit/Cycle146.lean only appended (plus top import lines)
ok: lean/Audit/Cycle147.lean only appended (plus top import lines)
ok: lean/Audit/Cycle148.lean only appended (plus top import lines)
ok: lean/Audit/Cycle149.lean only appended (plus top import lines)
ok: lean/Audit/Cycle150.lean only appended (plus top import lines)
ok: lean/Audit/Cycle151.lean only appended (plus top import lines)
ok: lean/Audit/Cycle152.lean only appended (plus top import lines)
ok: lean/Audit/Cycle153.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154FiniteExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154FiniteNonterminal.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154FiniteReserved.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154FiniteReservedPositive.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154HistoricalBranch.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154History.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154RecordedRequests.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154Value.lean only appended (plus top import lines)
ok: lean/Audit/Cycle154ValueRequests.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155ClassifierApplication.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155MixedProvenance.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155NominalRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155NonterminalApplication.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155Provenance.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155Recorded.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155RefreshedEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155Reserved.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155SelectedProvenance.lean only appended (plus top import lines)
ok: lean/Audit/Cycle155SuccessorBoundary.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156CatalogMultiArgument.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156CollectedRequests.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156MultiScalar.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156Refreshed.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156ReservedCatalog.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156ReservedEndpoint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle156RootIntervals.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157BindingSchema.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157Catalog.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157Compute.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157GeneratedIntervals.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157IntervalCoverage.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157MixedCapturedReplay.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157MixedCarrierRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157MixedInhabited.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157MixedReachable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157RecordedIntervals.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157UnaryRefinementCapture.lean only appended (plus top import lines)
ok: lean/Audit/Cycle157VariableClauseCatalog.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158HistoricalRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158HistoricalTree.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158Locations.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158MixedHistorical.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158MixedHistoricalExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158NestedBranch.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158NestedCarrier.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158NestedCurrent.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158NestedRefinement.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158RefreshSelection.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ReobservationGap.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158RevisionArgument.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158RevisionBridgeExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158RevisionCoverage.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ScalarChildEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ScalarChildExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ScalarChildIntervals.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ScalarChildReachable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ScalarGeneratedCoverage.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ScalarRegistryExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ScalarRegistryIntervals.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158Unary.lean only appended (plus top import lines)
ok: lean/Audit/Cycle158ValueRecordedCoverageLimit.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159CaptureMultiplicity.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159CaptureSemanticCollapse.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159PositiveNestedBranch.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159PositiveNestedInitial.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159PositiveNestedProjection.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapse.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseAllocation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseAllocationExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseBranch.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseBranchExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseEvidenceExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseOutputExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapsePointBoundary.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticCollapseSchema.lean only appended (plus top import lines)
ok: lean/Audit/Cycle159SemanticSchemaTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160ActualSchema.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160ActualSchemaOrigin.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160ActualSchemaOriginExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160ActualSchemaScope.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160CertifiedEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160CheckedNonpointEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160EmissionRequestIdentity.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160FinalDependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160ModeBoundary.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160NonpointEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160OperationalEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160Readiness.lean only appended (plus top import lines)
ok: lean/Audit/Cycle160StrictEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161ChildCaptureExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161ChildCaptureTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalCertified.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalChild.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalNamedEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalNamedExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalOldObstruction.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalParent.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161NonterminalScope.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161RecordedLeafPlans.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161RecordedRevision.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161RequestSnapshot.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161ValuePendingExclusion.lean only appended (plus top import lines)
ok: lean/Audit/Cycle161VariableLeafPlans.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162FinalDependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162MergedDependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledCutExclusion.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledGuardClosure.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledGuardedClassification.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledNamedExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledPendingExclusion.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledProjection.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledRecursiveExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledReservedExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledRootEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledSourceGuard.lean only appended (plus top import lines)
ok: lean/Audit/Cycle162SettledTreeEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163AliasSettlement.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163ConsumerResume.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163CoverageSeparation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163FinalDependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163RecordedSettlement.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163RecursiveConsumerObstruction.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163ReservationTimeline.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163SettledFiniteCoverage.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163SettledFiniteCoverageExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163SettledTerminalPrefix.lean only appended (plus top import lines)
ok: lean/Audit/Cycle163SettlementExamples.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164ExactRefreshChain.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164FinalDependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedBlockedOutput.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedCapturedTargets.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedConstantReady.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedConstantRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedCurrentEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedDisplayInstallation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedEvidenceTrace.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedInstallEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedOutputBinderScope.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedRecordedEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedRecordedTree.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedRecursiveExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedSemanticSettlement.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedSettlementResume.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedSiblingPrefix.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedTerminalInstallation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedTerminalObstruction.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164SharedTrustTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164TerminalEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle164TerminalRefreshObstruction.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165CapturedBranch.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165CapturedInputReady.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165CapturedInstallable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165CapturedInstallation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165CapturedProducer.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165CapturedRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165FinalDependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165IdentityCurrentEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165IdentityEvidenceExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165IdentityRefreshExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165Inherited164DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165SharedMetadata.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165SharedOrdinaryHistory.lean only appended (plus top import lines)
ok: lean/Audit/Cycle165SourceRetention.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166CapturedConsequences.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166CapturedProducer.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166CapturedScalarRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166CapturedTrustedBoundary.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166FinalProducerInspection.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166ProducerEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166ProducerGuard.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle166Resumption.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167AllPublicAxioms.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167CapturedAliasCountermodel.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167CapturedInputCountermodel.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167CapturedSettledProducerTrust.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167CapturedSettlement.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167EvidenceDelay.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167FinalEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167InheritedCapturedCoverage.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167InstallationBlocked.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167PromotionGateAndTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle167ReportTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168ActualTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168CapturedTreeGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168CapturedTreeTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168GenericTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168JournalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168Mixed.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168MixedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168OrdinaryRelocation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168RecordedRelocation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168RecursiveGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168RecursiveTransport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle168Source.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169AccessibilityGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169CoverageAccessible.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169CoverageGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169FiniteCoverage.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169FiniteDisplay.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169NamedGap.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169NamedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169NamedLeaf.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169NamedPersistence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169NamedPersistenceGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169NamedTree.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169Persistence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169Selected.lean only appended (plus top import lines)
ok: lean/Audit/Cycle169SharedStable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170AllGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170AssemblyPersistence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170AssemblyPersistenceGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170AssemblySize.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170AssemblySizeGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170BoundedAssembly.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170NamedCoverage.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170NamedCoverageGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170NamedCoveragePersistence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170NamedSelection.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170NamedSpine.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170NamedSpineExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170NamedSpineStable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle170PathBound.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171Assembly.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171AssemblyPersistence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171CheckedSpine.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171InputDiscovery.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171InspectionObservation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171LocalInspectionObservation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171NamedSpinePersistence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171RecursiveStrictness.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171RequestChecker.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171SpineCertificate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171SpineDiscovery.lean only appended (plus top import lines)
ok: lean/Audit/Cycle171SpinePersistence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle172CheckedSpineExact.lean only appended (plus top import lines)
ok: lean/Audit/Cycle172CheckerExact.lean only appended (plus top import lines)
ok: lean/Audit/Cycle172CheckerRegression.lean only appended (plus top import lines)
ok: lean/Audit/Cycle172CoverageInput.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173ActualEdge.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173DependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173FinalDependencyGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GeneralDictionary172CoverageSyntax.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GeneralDictionaryActualExample173.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GeneralDictionaryActualGroundComposition173.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GeneralDictionaryActualGroundExecutor173.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GeneralDictionaryActualRecorded173.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GeneralDictionaryActualStable173.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GeneralDictionaryActualV5173.lean only appended (plus top import lines)
ok: lean/Audit/Cycle173GroundExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174AgreedRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174AgreedRoleDescent.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174BoundedDiagnostic.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174CheckedExactness.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174CompletionGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174ComputedRoleDescent.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174ExtendedNamespaceGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174FinalNamespaceGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174GeneralDictionaryAgreedComposition174.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174GeneralDictionaryAgreedEdge174.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174GeneralDictionaryAgreedEvidence174.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174GeneralDictionaryAgreedExact174.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174GeneralDictionaryAgreedGround174.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174GeneralDictionaryAgreedRoleExamples174.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174HistoryObstruction.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174NamespaceGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174RefiningTrace.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174SearchOrder.lean only appended (plus top import lines)
ok: lean/Audit/Cycle174UniformCertificate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175AgreedFlexibleCompletion.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175AgreedFlexibleTrace.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175AllGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175CertifiedEvidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175CompactTable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175Completion.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175CoreGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175FirstGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175NominalOnlyRefresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175NominalViewRegression.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175Table.lean only appended (plus top import lines)
ok: lean/Audit/Cycle175TableExamples.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176Candidate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredFlexible.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredFootprint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredLedger.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredNonvacuous.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredReady.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredRecorded.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredRevision.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CenteredTree.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176CheckpointGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176ExpandedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176FirstGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176GroundLeaf.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176HeadFootprintRegression.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176Inhabited.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176LeafRegression.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176PublicDeclarations.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176PublicationGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176PublicationTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176Regression.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176SharedMerge.lean only appended (plus top import lines)
ok: lean/Audit/Cycle176ViewFootprint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle177BranchGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle177ExtendedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle177FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle177IntervalsGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle177MidpointGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle177PublicationGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle177RequestsGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle178ExtendedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle178FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle178NominalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle178ProducerGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle178RootGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle179FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle179Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle180FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle181AliasLedgerGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle181CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle181FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle181SemanticOverlap.lean only appended (plus top import lines)
ok: lean/Audit/Cycle182CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle182ProvenanceGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle183CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle183FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle183OriginGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle183RegisteredGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle184FourthGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle184Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle184MigrationTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle184PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle184SecondGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle184ThirdGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle185EffectsGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle185FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle185FullGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle185Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle185PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle185ReleaseGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle185SemanticTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle186CandidateGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle186Checkpoint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle186MechanismGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle186PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle186ReleaseGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle186SupportGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle187FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle187FrameGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle187FrameTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle187Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle187ProjectionGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle187PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle188BroadGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle188FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle188Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle188MixedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle188NominalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle188PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle188TransportGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189CompletePublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189EvidenceGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189FinalPublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189NamedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189PlainPublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189ProgressGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle189RegressionGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190AllPublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190CheckpointGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190CheckpointTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190CompletionGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190CompletionTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190InstalledTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190RegressionTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190ReleaseGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190RepairGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle190RepairTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle191Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle191PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle192Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle192PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle193Checkpoint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle193FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle193FinalTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle193Gate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194AccessibilityGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194AccessibilityTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194CheckpointGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194CheckpointTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194CombinedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194FinalTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194ReadbackTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194RecordedNodeGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194RecordedNodeTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194SelectedGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle194SelectedTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle195Catalogue.lean only appended (plus top import lines)
ok: lean/Audit/Cycle195Current.lean only appended (plus top import lines)
ok: lean/Audit/Cycle195KernelGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle195PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle196Executable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle196FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle196KernelGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle196PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle196Rooted.lean only appended (plus top import lines)
ok: lean/Audit/Cycle196RootedExample.lean only appended (plus top import lines)
ok: lean/Audit/Cycle196Transport.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197CheckpointGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197Evidence.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197Mixed.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197PublicTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197Refinement.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197RefinementGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197Syntax.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197SyntaxGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197SyntaxTypes.lean only appended (plus top import lines)
ok: lean/Audit/Cycle197Trace.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198CheckpointGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198FinalGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198Growing.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198Installed.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198Mixed.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198Obstruction.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198Reachable.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198Refining.lean only appended (plus top import lines)
ok: lean/Audit/Cycle198Slots.lean only appended (plus top import lines)
ok: lean/Audit/Cycle199AllocPriorCheck.lean only appended (plus top import lines)
ok: lean/Audit/Cycle199CompleteGate.lean only appended (plus top import lines)
ok: lean/Audit/Cycle199ExactPrior.lean only appended (plus top import lines)
ok: lean/Audit/Cycle202AllDeclarations.lean only appended (plus top import lines)
ok: lean/Audit/Cycle202SelectedTarget.lean only appended (plus top import lines)
ok: lean/Audit/Cycle203I35Target.lean only appended (plus top import lines)
ok: lean/Audit/Cycle204JoinTarget.lean only appended (plus top import lines)
ok: lean/Audit/Cycle204Public.lean only appended (plus top import lines)
ok: lean/Audit/Cycle206DefaultGap.lean only appended (plus top import lines)
ok: lean/Audit/Cycle206Semantic.lean only appended (plus top import lines)
ok: lean/Audit/Cycle208DefaultRepair.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalBudget.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCaptureAssembly.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredClassLocal.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredCompletionAliasObstruction.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHead.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadAlloc.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadAllocMergeConflict.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadAllocV7.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadAvailabilityOrder.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMat.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatCanonicalClosure.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatCompletionCollision.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatGroundCover.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatHeadReadback.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatRefreshRegression.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatSemanticAncestry.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatStep.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadMatTrustedCache.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadStep.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadStepMaterialization.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCenteredHeadWF.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalCompoundInputs.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalDepthBound.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalDownstream.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalFreshAnalysis.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalGroundFactorization.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalGroundInputs.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalGroundReadback.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalHoleElimination.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalPointBudget.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalPointClass.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalProvenanceCheckpoint.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalRecursivePeeling.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSettledCover.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSharedOrigins.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSourceFrontier.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupport.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupportOrder.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalUnsettledDeferral.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalValueProvenance.lean only appended (plus top import lines)
ok: lean/Audit/GroundHeadMatching.lean only appended (plus top import lines)
ok: lean/Audit/HolePhaseOpenProducers.lean only appended (plus top import lines)
ok: lean/Audit/MatEmptyLeaf199.lean only appended (plus top import lines)
ok: lean/Audit/MatGuardObstruction199.lean only appended (plus top import lines)
ok: lean/Audit/MatGuardTrace199.lean only appended (plus top import lines)
ok: lean/Audit/MatGuardWitness199.lean only appended (plus top import lines)
ok: lean/Audit/MatInputAssembly201.lean only appended (plus top import lines)
ok: lean/Audit/MatInputV7Tree201.lean only appended (plus top import lines)
ok: lean/Audit/MatPriorConflict199.lean only appended (plus top import lines)
ok: lean/Audit/MatPriorConflictLocal199.lean only appended (plus top import lines)
ok: lean/Audit/MatPriorConflictSource199.lean only appended (plus top import lines)
ok: lean/Audit/MatScalarConflict200.lean only appended (plus top import lines)
ok: lean/Audit/MatScalarOutputs200.lean only appended (plus top import lines)
ok: lean/Audit/MatScalarScope200.lean only appended (plus top import lines)
ok: lean/Audit/MatSelectedScalar200.lean only appended (plus top import lines)
ok: lean/Audit/MatStableScalar200.lean only appended (plus top import lines)
ok: lean/Audit/MatTerminalAssembly200.lean only appended (plus top import lines)
ok: lean/Audit/MatVariableNode199.lean only appended (plus top import lines)
ok: lean/Audit/NonpointCertified.lean only appended (plus top import lines)
ok: lean/Audit/NonpointCertifiedOutput.lean only appended (plus top import lines)
ok: lean/Audit/NonpointCollapse.lean only appended (plus top import lines)
ok: lean/Audit/NonpointExample.lean only appended (plus top import lines)
ok: lean/Audit/NonpointOutput.lean only appended (plus top import lines)
ok: lean/Audit/NonpointStrict.lean only appended (plus top import lines)
ok: lean/Audit/NonpointStrictOutput.lean only appended (plus top import lines)
ok: lean/Audit/NormalizedCaptureAssemblyProgress.lean only appended (plus top import lines)
ok: lean/Audit/Point179.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
ok: lean/Audit/SharedDiscovery179.lean only appended (plus top import lines)
ok: lean/Audit/SourceProducerClosure.lean only appended (plus top import lines)
ok: lean/Audit/SourceSyntaxRefinement.lean only appended (plus top import lines)
ok: lean/Audit/UniformCenteredProduction.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

```

## Full102-declaration axiom output

```text
'Yulang.GeneralDictionaryDefaultBodyTransport209.actual_only' depends on axioms: [propext]
'Yulang.GeneralDictionaryDefaultBodyTransport209.actuals_only' depends on axioms: [propext]
'Yulang.GeneralDictionaryDefaultBodyTransport209.actual_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultBodyTransport209.compile_equal' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultBodyTransport209.body_holds_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultBodyTransport209.actual_variables' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultBodyTransport209.semantic_body_variables' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultBodyTransport209.body_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultConfiguration209.seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultConfiguration209.frame_constructors' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultConfiguration209.stored' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultConfiguration209.reinspection_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.equivalent_refl' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.equivalent_trans' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.primitive_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.list_length' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.list_get' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.list_symm' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.nominal_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.value_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultExpression209.values_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrame209.frame_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrame209.certificate_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrame209.instance_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrame209.childrenFunctional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReadback209.unique_readback' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReadback209.anyModel_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReadback209.model_independent_readback' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReadback209.node_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReadback209.node_current_frame_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReinspection209.body_same' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReinspection209.effects_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultReinspection209.packet_reinspect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultReinspection209.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultReinspection209.evidence_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultReinspection209.generated_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedCenters209.centers_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedCenters209.recenter_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedCenters209.recenter_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedCenters209.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedCenters209.nominal_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedExamples209.interval_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedExamples209.interval_collapsed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedExamples209.nonpoint_centers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultCollapsedExamples209.nonpoint_default_transport' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultCurrentCertificate209.frame_data' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultCurrentCertificate209.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultCurrentCertificate209.instance_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultCurrentCertificate209.node_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultFrameSemantics209.declaration' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrameSemantics209.binder' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrameSemantics209.body_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrameSemantics209.class_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultFrameSemantics209.model_class_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.similar_of_observations' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.head_similar' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.actual_similar' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.append_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.tested_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.schema_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.schemas_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.head_schema_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.point_head_schema_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultHeadTransport209.current_frame_schema' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.erase_report' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.located_stored' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.report_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.reinspection_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.observed_stored' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.nominal_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.nominal_evidence_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultObserved209.nominal_generated_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultOutputBridge209.stored_visible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultOutputBridge209.declaration_of_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultOutputBridge209.default_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultOutputBridge209.default_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultPointTransport209.centers_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultPointTransport209.default_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultPointTransport209.stored_default_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultReplayExamples209.total_at_center' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultReplayExamples209.distinct_inputs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultReplayExamples209.replay_one_to_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultReplayExamples209.distinct_total_packets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.recentered_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_evidence_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.generated_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_generated_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.point_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.distinct_centers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.point_default' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.distinct_default_transport' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.interval_bottom_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.interval_int_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.interval_not_point' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.interval_default_bottom' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.interval_default_int_false' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryDefaultTransportExamples209.point_premise_necessary' depends on axioms: [propext, Quot.sound]

```
