import Yulang.GeneralDictionaryVersionedReachable232
import Yulang.GeneralDictionaryVersionedSelectionFacts232
import Yulang.GeneralNominalVersionedDiagnosticLaws232
import Yulang.GeneralNominalVersionedReplayEffects232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedSelected232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedInstalled232
open GeneralDictionaryVersionedReconstruction231 (replayed)
open GeneralNominalVersionedJournal232

theorem packet (valid : Models installed m) : GeneralNominalVersionedPlans231.Holds replayed m :=
  (GeneralNominalVersionedInstallation231.replay_holds_iff currentPlan m).mpr
    (valid.2.1 currentPlan actual_plan_recorded)

theorem effects (valid : Models installed m) :
    GeneralNominalVersionedEffects231.ClassEffects installed.core root replayed m :=
  (GeneralNominalVersionedReplayEffects232.replay_class_effects_iff installed.core root currentPlan m).mpr
    (valid.2.2 effect actual_effect_recorded).2

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready installed.core root replayed := by
  apply (GeneralNominalVersionedReplayEffects232.replay_ready_iff installed.core root currentPlan).mpr
  exact (GeneralNominalVersionedFrameTransport232.ready_iff
    (fun output => requests_iff (output := output))).mpr GeneralDictionaryUpper230Selected.ready

theorem no_merged : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict installed root := by
  rintro ⟨⟨first,last,member,_,_⟩,_⟩
  change (first,last) ∈ ([] : List (Nat × Nat)) at member
  cases member

theorem selected : GeneralNominalVersionedDiagnostic232.Local registry installed root (.selected declaration.id []) :=
  GeneralNominalVersionedDiagnosticLaws232.selected_of_model
    GeneralDictionaryVersionedSelectionFacts232.safe
    GeneralDictionaryVersionedSelectionFacts232.unique
    GeneralDictionaryVersionedAcyclic232.installed_model
    GeneralDictionaryVersionedEvidence232.frame ready
    (packet GeneralDictionaryVersionedAcyclic232.installed_model)
    (effects GeneralDictionaryVersionedAcyclic232.installed_model) no_merged

theorem selected_with_evidence :
    GeneralNominalVersionedMigration232.Reachable registry context root installed ∧
    (∃ m, Models installed m) ∧
    GeneralNominalVersionedDiagnostic232.Local registry installed root (.selected declaration.id []) ∧
    ∀ m, Models installed m →
      GeneralNominalVersionedEvidence231.Evidence registry installed.core m root (.node declaration.id []) :=
  ⟨GeneralDictionaryVersionedReachable232.reachable,inhabited,selected,
    fun _ => GeneralDictionaryVersionedEvidence232.evidence⟩

end Yulang.GeneralDictionaryVersionedSelected232
