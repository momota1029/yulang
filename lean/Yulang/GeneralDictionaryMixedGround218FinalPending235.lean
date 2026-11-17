import Yulang.GeneralDictionaryMixedGround218FinalOutcome235
set_option backward.isDefEq.respectTransparency false
/-! Exact diagnostic of the new point child at the concrete final state.
This prevents mistaking the stable EvidenceAt law for a completed root dictionary. -/
namespace Yulang.GeneralDictionaryMixedGround218FinalPending235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Reinstall (newChild)
open GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryMixedGround218FinalRegression235 (sites)
open GeneralDictionaryMixedGround218FinalOutcome235 (new_root_pending)

theorem equal_outputs (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs finalState.core focus
      GeneralDictionaryGroundCopy218Install.model := by
  intro output member
  rw [GeneralDictionaryMixedGround218RootCommitted235.requests_empty sites focus] at member
  cases member

theorem no_merged_conflict : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict finalState newChild.occurrence :=
  GeneralNominalVersionedMergedConflict232.models_exclude_conflict final_model
    (fun focus _ => equal_outputs focus) (equal_outputs newChild.occurrence)

theorem no_sharing_conflict : ¬ GeneralNominalVersionedDiagnostic232.SharingConflict registry finalState newChild.occurrence := by
  rintro ⟨_,_,_,safe,_⟩
  exact safe.1 new_root_pending

theorem pending : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState newChild.occurrence .pending :=
  .ordinary no_sharing_conflict (.ordinary no_merged_conflict (.pending new_root_pending))

end Yulang.GeneralDictionaryMixedGround218FinalPending235
