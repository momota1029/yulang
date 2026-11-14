import Yulang.GeneralNominalCenteredAdministrativeComposition
import Yulang.GeneralNominalCenteredSelectionCounterexample

/-! The reachable duplicate-Display obstruction now has the intended
administrative pending diagnostic. The source root's selection is preserved. -/
namespace Yulang.GeneralNominalCenteredAdministrativeExamples
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalCenteredSelectionCounterexample
open GeneralDictionaryEarlyMergeScalarExample (registry children)
open GeneralDictionaryEarlyMergeExample (child)
open GeneralNominalCenteredPointMergeExample (centerSite)
open GeneralNominalExamples (displayRoot)

theorem source_selected : Local registry cstart displayRoot (.selected 1 children) :=
  (initial_local_iff registry _ displayRoot _).mpr cselected

theorem duplicate_not_ready : ¬ AdministrativeReady cbefore (child 10) := by
  have centers : cbefore.sites = [cplan.input,centerSite 10,centerSite 11] :=
    GeneralNominalCenteredPointMergeExample.center_sites
  apply required_merge_not_ready (centerSite 10) (centerSite 11)
  · rw [centers]; simp
  · rw [centers]; simp
  · exact ⟨rfl,.cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil⟩
  · intro alias
    have equal : ∀ a b, GeneralNominalSaturationState.Alias cbefore.erased.current a b → a = b := by
      intro a b related
      induction related with
      | refl => rfl
      | edge member => cases member
      | symm h ih => exact ih.symm
      | trans one two ih₁ ih₂ => exact ih₁.trans ih₂
    exact GeneralDictionaryEarlyMergeScalarJoint.distinct_children (equal _ _ alias)

theorem duplicate_pending : Local registry cbefore (child 10) .pending := by
  have old := child_selected 10
  cases old with
  | selected safe unique =>
    exact administrative_pending safe.1 safe.2.1 safe.2.2.1 duplicate_not_ready

theorem reachable_duplicate_pending :
    B4TargetV5.Reachable (boundary GeneralDeclarationExamples.roles) registry displayRoot cbefore ∧
      Local registry cbefore (child 10) .pending :=
  ⟨ground_reachable,duplicate_pending⟩

end Yulang.GeneralNominalCenteredAdministrativeExamples
