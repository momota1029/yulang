import Yulang.GeneralDictionarySettledFiniteCoverage
import Yulang.GeneralDictionarySettledRecursiveExample

/-! A nonempty historical journal plus an unrecorded scalar child inhabits the
syntax/history coverage of the genuine settled root theorem. -/
namespace Yulang.GeneralDictionarySettledFiniteCoverageExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralDictionarySupportRecursiveClosure GeneralNominalExamples
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries GeneralNominalSaturationState

private theorem alias_equal {first last : Nat} (related : Alias finish.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem leaf_shape : GeneralDictionaryFiniteAliasJoint.Shape finish.current.context registry
    displayChild intDisplay int_display_checked := by
  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
  exact ⟨GeneralDictionaryScalarLeaf.recursiveDisplayShape⟩

theorem leaf_covered : GeneralDictionaryFiniteAliasJoint.Covered registry finish
    displayChild intDisplay int_display_checked := by
  intro site related
  have member := related.1
  rw [sites_exact] at member
  rcases List.mem_cons.mp member with same | other
  · subst site
    have impossible : displayChild.identity ≠ displayRoot.identity := by decide +kernel
    exact False.elim (impossible (alias_equal related.2))
  · have same := List.mem_singleton.mp other
    subst site
    exact ⟨leaf_shape,3,[],supported_leaf_selected⟩

theorem covered : GeneralDictionarySettledFiniteCoverage.Covered registry finish displayRoot := by
  intro focus generated key children selected
  rcases generated_cases focus generated with same | same
  · subst focus
    exact Or.inl ⟨packet,List.mem_singleton_self _,rfl⟩
  · subst focus
    exact Or.inr ⟨intDisplay,by simp,int_display_checked,leaf_shape,leaf_covered⟩

theorem growth : ∀ recorded ∈ finish.current.packets,
    GeneralDictionaryOrdinaryTrace.Extension recorded.context finish.current.context := by
  intro recorded member
  have same := List.mem_singleton.mp member
  subst recorded
  exact GeneralDictionaryOrdinaryTrace.packet_extension packet

/-- Derived via the new coverage theorem, not by using prior Evidence as a premise. -/
theorem all_models : ∀ assignment, Models finish.current assignment →
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context assignment
      displayRoot (.node 1 [.node 3 []]) :=
  GeneralDictionarySettledFiniteCoverage.root_dictionary_all_models registry displayRoot finish
    GeneralDictionarySettledRecursiveExample.reachable growth
    GeneralDictionarySettledRecursiveExample.stable covered _
    GeneralDictionarySettledRecursiveExample.classified

/-- Explicitly nonvacuous and recursive, with a nonempty packet journal. -/
theorem realized : finish.current.packets ≠ [] ∧ Models finish.current model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model
      displayRoot (.node 1 [.node 3 []]) :=
  ⟨nonempty_journal,current_model,all_models model current_model⟩
end Yulang.GeneralDictionarySettledFiniteCoverageExample
