import Yulang.GeneralRebaseVersionDelta283
import Yulang.GeneralRebaseLooseDelta283
import Yulang.GeneralRebaseOptionalOverwrite282

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseCachedFixtures283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseInstallCache283 (Valid interpret add forward)
open GeneralRebaseIncrementalGate283 (Gate changed)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCachedDriver283 (Move Initial Snapshot)
open GeneralRebaseHistoryOrder282 (decode history)
open GeneralRebasePrivateStore282 (Joint)
open GeneralRebaseSliceEvidence283 (reads Evidence exact_finite_query)
open GeneralRebaseSliceJournal283 (journalReads sliced)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty reachable_legacy_empty)
open GeneralRebaseWholeJournal282 (View exact_view)
open GeneralDictionaryReadback (Payload)

theorem slice_live {s : State roles} (reach : Reachable registry root s) (r : Registry)
    (focus : Occurrence roles) (payload : Payload) (base : Assignment) :
    View s r focus payload base ↔ ∃ family,
      let defs := GeneralRebaseInstallCache283.initial s
      let m := sliced defs (journalReads s ++ reads family) base
      Models s m ∧ Evidence family r s m focus payload := by
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable reach
  have valid := GeneralRebaseInstallCache283.initial_valid record
  have same := GeneralRebaseInstallCache283.interpret_exact valid record base
  exact (exact_view reach r focus payload base).trans
    (show Joint s r focus payload (decode s base) ↔ _ from same ▸
      exact_finite_query valid record (reachable_legacy_empty reach) r base focus payload)

theorem source_query {s : State roles} (reach : Reachable registry root s) (r : Registry)
    (focus : Occurrence roles) (payload : Payload) (a : Assignment)
    (given : Joint s r focus payload a) :
    ∃ family, let defs := GeneralRebaseInstallCache283.initial s
      let m := sliced defs (journalReads s ++ reads family) a
      Models s m ∧ Evidence family r s m focus payload :=
  (slice_live reach r focus payload a).mp
    ((exact_view reach r focus payload a).mpr (GeneralRebaseHistoryOrder282.preserves_joint reach given))

namespace Display
open GeneralNominalExamples (registry displayRoot)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (after effect compiled)

theorem source_start : Reachable registry displayRoot before :=
  ⟨_,GeneralRebaseDisplayStep276.initial_source,.refl⟩

theorem move : Move registry displayRoot (Initial before) ⟨after,add (Initial before).defs effect⟩ := by
  have seen := source_start
  have valid := GeneralRebaseInstallCache283.initial_valid (GeneralNominalVersionedMixedSeedLedger237.reachable seen)
  have ready := GeneralRebaseCompiledInstall277.installable
  have setup := GeneralRebaseCompiledInstall282.setup ready
  exact ⟨seen,valid,Or.inr ⟨effect,.root,setup,GeneralRebaseCompiledInstall277.novel,rfl,
    (GeneralRebaseIncrementalGate283.enabled valid seen setup).mp ready⟩⟩

theorem nonleaf (a : Assignment) (good : Models after a) :
    ∃ family, let defs := GeneralRebaseInstallCache283.initial after
      let m := sliced defs (journalReads after ++ reads family) a
      Models after m ∧ Evidence family compiled after m displayRoot (.node 1 [.node 3 []]) :=
  source_query GeneralRebaseCompiledFixtures282.Display.reached compiled displayRoot (.node 1 [.node 3 []])
    a ⟨good,GeneralRebaseCompiledEvidence277.real_nonleaf a good⟩

end Display

namespace Default
open GeneralDictionaryDefaultGap206Source (registry root model)
open GeneralDictionaryMixedGap206Refresh234 (refreshed reachable model_retained)

theorem body_kept : ∃ family, let defs := GeneralRebaseInstallCache283.initial refreshed
    let m := sliced defs (journalReads refreshed ++ reads family) model
    Models refreshed m ∧ Evidence family (GeneralNominalCenteredHeadAllocEncoding.registry registry) refreshed m root (.node 37 []) :=
  source_query reachable _ root (.node 37 []) model
    ⟨model_retained,GeneralDictionaryMixedGap206Evidence234.evidence model model_retained⟩

end Default

namespace Optional
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (effect installed installed_model)
open GeneralRebaseOptionalOverwrite282 (point_reached)
open GeneralDictionaryOptionalInitial229 (sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryVersionedBothModel233 (extended)

theorem candidate : ∃ base, Gate point effect (Initial point).defs (interpret (Initial point).defs base) :=
  (GeneralRebaseIncrementalGate283.candidate
    (GeneralRebaseInstallCache283.initial_valid (GeneralNominalVersionedMixedSeedLedger237.reachable point_reached))
    point_reached (show effect.snapshot = point.core from rfl)).mpr
      ⟨extended,GeneralDictionaryVersionedSecondInstall233.installation_models⟩

theorem root_payload : ∃ family, let defs := GeneralRebaseInstallCache283.initial installed
    let m := sliced defs (journalReads installed ++ reads family) extended
    Models installed m ∧ Evidence family (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry)
      installed m root (.node declaration.id []) :=
  source_query GeneralRebaseTerminalMixedRefresh274.mixed_reachable _ root (.node declaration.id []) extended
    ⟨installed_model,GeneralDictionaryVersionedSecondInstall233.evidence installed_model⟩

end Optional

end Yulang.GeneralRebaseCachedFixtures283
