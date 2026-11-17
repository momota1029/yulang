import Yulang.GeneralDictionaryCompoundChildPending238
import Yulang.GeneralNominalVersionedMixedSelectedFrame235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundVacuity238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundPoint238 GeneralDictionaryCompoundSites238
open GeneralDictionaryCompoundObstruction238
open GeneralNominalCenters GeneralSourceDictionaries

theorem current_children : GeneralNominalVersionedFrame231.children currentPlan.packet = [childSite.occurrence] := by
  have exactList : GeneralNominalVersionedFrame231.children currentPlan.packet =
      [(GeneralNominalVersionedFrame231.childSite currentPlan child signature).occurrence] := by
    unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
      GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
    rfl
  rw [GeneralDictionaryCompoundReplay238.child_site] at exactList
  exact exactList

theorem reached_cases (demand : Occurrence roles)
    (reached : demand = root ∨ GeneralNominalSaturationState.Generated point.core.erased.current root demand) :
    demand = root ∨ demand = childSite.occurrence := by
  rcases reached with same | generated
  · exact Or.inl same
  · obtain ⟨raw,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
      (GeneralNominalVersionedMixedTrace235.reachable reachable).1 generated
    rw [raw_sites] at present
    rcases List.mem_cons.mp present with equal | present
    · subst raw; exact Or.inl same.symm
    · cases List.mem_singleton.mp present
      exact Or.inr same.symm

/-- The present fixture is NOT an EvidenceNode counterexample: the generated
child has no current evidence, so the node-rule antecedent is impossible. -/
theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry point root := by
  intro model _valid demand key children dictionaries reached _stable _childStable chosen childEvidence
  obtain ⟨plan,framed,childrenEq⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame reachable chosen
  rcases reached_cases demand reached with same | same
  · subst demand
    have planEq := GeneralDictionaryCompoundNoInstance238.frame_plan framed
    subst plan
    rw [current_children] at childrenEq
    cases childrenEq
    cases childEvidence with
    | cons one _ => exact False.elim (GeneralDictionaryCompoundChildPending238.no_evidence model _ one)
  · subst demand
    exact False.elim (GeneralDictionaryCompoundChildPending238.no_frame key plan framed)

end Yulang.GeneralDictionaryCompoundVacuity238
