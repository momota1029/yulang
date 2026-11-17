import Yulang.GeneralDictionaryCompoundNoInstance239
import Yulang.GeneralNominalVersionedMixedSelectedFrame235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundVacuity239
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundRefresh239 GeneralDictionaryCompoundRefreshStep239 GeneralDictionaryCompoundSites238
open GeneralDictionaryCompoundObstruction239
open GeneralNominalCenters GeneralSourceDictionaries

 theorem child_site (signature : child.Signature roles) :
    GeneralNominalVersionedFrame231.childSite currentPlan child signature =
      GeneralNominalVersionedFrame231.childSite GeneralDictionaryCompoundObstruction238.oldPlan child signature := by
  unfold GeneralNominalVersionedFrame231.childSite GeneralNominalVersionedFrame231.clauseChild
    GeneralDictionaryEmissionPlans.occurrence GeneralDeclarationDemands.emit
    GeneralDeclarationDemands.childDemand GeneralNominalVersionedFrame231.frame
    GeneralNominalVersionedFrame231.emittedCenter
  dsimp only
  congr 1
  congr 1
  congr 1
  all_goals
    funext index
    have same : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
    subst index
    rfl

theorem current_children : GeneralNominalVersionedFrame231.children currentPlan.packet = [childSite.occurrence] := by
  have exactList : GeneralNominalVersionedFrame231.children currentPlan.packet =
      [(GeneralNominalVersionedFrame231.childSite currentPlan child signature).occurrence] := by
    unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
      GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
    rfl
  rw [child_site] at exactList
  exact exactList

theorem reached_cases (demand : Occurrence roles)
    (reached : demand = root ∨ GeneralNominalSaturationState.Generated refreshed.core.erased.current root demand) :
    demand = root ∨ demand = childSite.occurrence := by
  rcases reached with same | generated
  · exact Or.inl same
  · obtain ⟨raw,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
      (GeneralNominalVersionedMixedTrace235.reachable reachable).1 generated
    change raw ∈ GeneralDictionaryCompoundPoint238.point.core.erased.current.sites at present
    rw [raw_sites] at present
    rcases List.mem_cons.mp present with equal | present
    · subst raw; exact Or.inl same.symm
    · cases List.mem_singleton.mp present
      exact Or.inr same.symm

/-- After the actual child refresh the node-rule premise is still impossible,
now by a finished head mismatch rather than missing physical source slots. -/
theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry refreshed root := by
  intro model _valid demand key children dictionaries reached _stable _childStable chosen childEvidence
  obtain ⟨plan,framed,childrenEq⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame reachable chosen
  rcases reached_cases demand reached with same | same
  · subst demand
    have planEq := GeneralDictionaryCompoundNoInstance239.frame_plan framed
    subst plan
    rw [current_children] at childrenEq
    cases childrenEq
    cases childEvidence with
    | cons one _ => exact False.elim (GeneralDictionaryCompoundChild239.no_evidence model _ one)
  · subst demand
    exact False.elim (GeneralDictionaryCompoundChild239.no_frame key plan framed)

end Yulang.GeneralDictionaryCompoundVacuity239
