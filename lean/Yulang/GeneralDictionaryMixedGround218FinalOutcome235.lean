import Yulang.GeneralDictionaryMixedGround218FinalRegression235
import Yulang.GeneralDictionaryMixedGround218FinalRejection235
set_option backward.isDefEq.respectTransparency false
/-! Final 218 acceptance bundle: actual source reachability, nonempty models,
full mixed stability and EvidenceAt, with the old generated child explicitly
rejected. The new child's raw RootPending is stated, not a root dictionary. -/
namespace Yulang.GeneralDictionaryMixedGround218FinalOutcome235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryMixedGround218FinalRegression235 (sites stable evidenceAt)
open GeneralDictionaryMixedGround218Leaf235 (oldChild)
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234

theorem old_generated : GeneralNominalSaturationState.Generated finalState.core.erased.current root oldChild := by
  apply GeneralNominalSaturationState.Generated.child .root
  rw [sites.2.2,← GeneralDictionaryMixedGround218LeafFrame235.child_eq]
  exact List.mem_cons_self

theorem new_generated : GeneralNominalSaturationState.Generated finalState.core.erased.current root
    GeneralDictionaryGroundCopy218Reinstall.newChild.occurrence := by
  apply GeneralNominalSaturationState.Generated.child .root
  rw [sites.2.2]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem new_root_pending : GeneralNominalState.RootPending finalState.core.erased.current.context.state
    GeneralDictionaryGroundCopy218Reinstall.newChild.occurrence.demand :=
  GeneralDictionaryMixedGround218PointStable235.new_pending allocated reserved ordinary
    (congrArg GeneralNominalCandidates.Context.state final_context)

theorem source_regression :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked sourceRegistry ∧
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root finalState ∧
    (∃ model, Models finalState model) ∧ Stable registry finalState root ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry finalState root ∧
    GeneralNominalSaturationState.Generated finalState.core.erased.current root oldChild ∧
    GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState oldChild .rejected :=
  ⟨⟨rfl,source_checked⟩,GeneralDictionaryMixedGround218FinalState235.reachable,⟨_,final_model⟩,
    stable,evidenceAt,old_generated,GeneralDictionaryMixedGround218FinalRejection235.rejected⟩

end Yulang.GeneralDictionaryMixedGround218FinalOutcome235
