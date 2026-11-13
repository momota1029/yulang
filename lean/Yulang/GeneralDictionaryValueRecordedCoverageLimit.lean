import Yulang.GeneralDictionaryRecordedCoverageLimit
import Yulang.GeneralNominalValueBoundary

/-! Actual Value stability does not force a journal packet for a selected leaf.
This is a limitation of historical-only coverage, not a failure of dictionary
soundness. The fixture is reachable, modeled and has a nonempty journal. -/
namespace Yulang.GeneralDictionaryValueRecordedCoverageLimit
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)

theorem value_step : GeneralNominalValueSteps.Step registry displayRoot start finish := by
  apply GeneralNominalValueSteps.source_install start packet Generated.root enabled
  · intro committed
    have impossible := committed.2 displayChild (by rw [children_exact]; simp)
    cases impossible
  · exact GeneralNominalSupportExamples.display_guard

theorem reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles)
    registry displayRoot finish :=
  ⟨start,⟨context true,initial_source,rfl⟩,.tail .refl value_step⟩

theorem stable : GeneralNominalValueSteps.Stable registry finish displayRoot := by
  intro focus generated after update
  exact GeneralDictionarySupportRecursiveClosure.stable focus generated after
    (GeneralNominalDownstreamSteps.at_old (GeneralNominalValueSteps.at_old update))

private theorem all_heads (slot : Fin 2) :
    ∃ test observation, GeneralNominalSupport.Head (state true) ((state true).base.source slot) test observation ∧
      GeneralNominalSupport.Head current.state (current.state.base.source slot) test observation := by
  have bounded := slot.isLt
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl,GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl,GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl⟩

private theorem guard (root : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, root.demand.arguments index = (slot.val,slot.val)) :
    GeneralNominalSupport.DecisionGuard finish registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    rw [show (root.demand.arguments index).1 = slot.val by rw [args index]]
    obtain ⟨test,observation,source,seen⟩ := all_heads slot
    exact GeneralNominalSupport.source_ready finish slot.val test observation observation source seen []
  · intro declaration visible role bounds located read member
    obtain ⟨test,observation,source,seen⟩ := all_heads read
    exact GeneralNominalSupport.source_ready finish read.val test observation observation source seen []

theorem leaf_selected : GeneralNominalValueBoundary.Local registry finish displayChild (.selected 3 []) :=
  GeneralNominalValueBoundary.selected_supported GeneralDictionarySupportRecursiveClassification.leaf_selected []
    (GeneralNominalValueSupport.source_decision registry finish displayChild (guard displayChild 1 (fun _ => rfl)))

/-- No all-model or historical-support hypothesis: even the actual Value
boundary can select a generated, Stable leaf without recording its packet. -/
theorem stable_selected_unrecorded :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧
    GeneralNominalValueSteps.Stable registry finish displayRoot ∧
    Generated finish.current displayRoot displayChild ∧
    GeneralNominalValueBoundary.Local registry finish displayChild (.selected 3 []) ∧
    GeneralNominalValueSteps.Stable registry finish displayChild ∧
    ¬ ∃ packet ∈ finish.current.packets, packet.site.occurrence = displayChild := by
  refine ⟨reachable,current_model,nonempty_journal,stable,
    GeneralDictionaryRecordedCoverageLimit.leaf_generated,leaf_selected,?_,
    GeneralDictionaryRecordedCoverageLimit.no_leaf_packet⟩
  intro focus reached after update
  exact stable focus (generated_trans GeneralDictionaryRecordedCoverageLimit.leaf_generated reached) after update
end Yulang.GeneralDictionaryValueRecordedCoverageLimit
