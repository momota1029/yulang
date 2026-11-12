import Yulang.GeneralDictionarySupportOrdinaryExecution
import Yulang.GeneralDictionarySupportRecursiveTrace

/-! A reachable modeled stable successful fixture has an unrecorded selected
leaf. Requiring every selected focus to have a journal packet is therefore
strictly stronger than the intended V5 behavior; this is NOT a V5 counterexample. -/
namespace Yulang.GeneralDictionaryRecordedCoverageLimit
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralSourceDictionaries

/-- The entire successful trace is in the proved ordinary operational subclass. -/
theorem ordinary_trace : B4Target.Steps
    (GeneralDictionarySupportOrdinaryExecution.Step registry displayRoot) start finish := by
  apply B4Target.Steps.tail B4Target.Steps.refl
  refine ⟨displayRoot,.root,.install packet [] enabled ?_ GeneralNominalSupportExamples.display_guard⟩
  intro committed
  have impossible := committed.2 displayChild (by rw [children_exact]; simp)
  cases impossible

theorem no_leaf_packet : ¬ ∃ p ∈ finish.current.packets, p.site.occurrence = displayChild := by
  rintro ⟨p,member,same⟩
  have identical : p = packet := List.mem_singleton.mp member
  subst p
  have identity := congrArg Occurrence.identity same
  contradiction

theorem leaf_generated : Generated finish.current displayRoot displayChild := by
  apply Generated.child Generated.root
  rw [GeneralDictionarySupportRecursiveClosure.edges_exact]
  exact List.mem_singleton_self _

theorem leaf_stable : GeneralNominalSupportSteps.Stable registry finish displayChild := by
  intro focus reached after update
  exact GeneralDictionarySupportRecursiveClosure.stable focus
    (generated_trans leaf_generated reached) after update

/-- Even reachable + modeled + stable + selected does not force a matching
historical packet. This concrete leaf already has valid semantic evidence. -/
theorem stable_selected_unrecorded :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    GeneralNominalSupportBoundary.Local registry finish displayChild (.selected 3 []) ∧
    GeneralNominalSupportSteps.Stable registry finish displayChild ∧
    ¬ ∃ p ∈ finish.current.packets, p.site.occurrence = displayChild :=
  ⟨actual_reachable,current_model,GeneralDictionarySupportRecursiveClosure.stable,
    supported_leaf_selected,leaf_stable,no_leaf_packet⟩

end Yulang.GeneralDictionaryRecordedCoverageLimit
