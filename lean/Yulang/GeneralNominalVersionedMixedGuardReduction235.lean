import Yulang.GeneralNominalVersionedMixedCurrentCandidate235
import Yulang.GeneralNominalCenteredInspection
set_option backward.isDefEq.respectTransparency false
/-! Position completeness and every candidate-cycle guard follow from actual
selected classification and the current versioned Frame, not added premises. -/
namespace Yulang.GeneralNominalVersionedMixedGuardReduction235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedMixedCurrentCandidate235
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem positions
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state demand (.selected key children))
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core demand selectedKey plan) :
    GeneralNominalVersionedCycles232.Safe state plan := by
  refine ⟨GeneralNominalCenteredInspection.plan_complete plan ?_,?_⟩
  · have located := frame.located
    rw [← frame.occurrence_eq,← plan.input_exact] at located
    exact located
  · intro entry member cycle
    exact (selected_safe selected).2.2.1 (Or.inr ⟨plan,frame.key_eq.symm ▸ frame,entry,member,cycle⟩)

theorem alternatives
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state input.occurrence (.selected key children)) :
    AlternativesSafe registry state input := by
  intro plan _ frame
  exact positions selected frame

theorem current
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (occurrence : effect.plan.packet.site.occurrence = demand)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state demand (.selected key children))
    (materialized : (GeneralNominalVersionedPlans231.emittedSchema effect.plan).unknown = false)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
    (common : ∃ model, GeneralNominalVersionedInstall232.InstallationModels state effect model) :
    Current registry state demand effect := by
  have frame := effect.frame
  rw [registryEq,snapshot,occurrence] at frame
  refine ⟨registryEq,snapshot,occurrence,materialized,choice,positions selected frame,?_,common⟩
  apply alternatives
  have same : effect.plan.input.occurrence = demand := effect.plan.input_exact.trans occurrence
  exact same.symm ▸ selected

theorem installable_iff
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state effect.plan.packet.site.occurrence (.selected key children))
    (cache : GeneralNominalVersionedMixedKernelCache234.Valid state) :
    Installable registry state effect ↔
      (GeneralNominalVersionedPlans231.emittedSchema effect.plan).unknown = false ∧
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
      ∃ model, GeneralNominalVersionedInstall232.InstallationModels state effect model := by
  constructor
  · intro enabled; exact ⟨enabled.materialized,enabled.choice,enabled.common⟩
  · rintro ⟨materialized,choice,common⟩
    exact GeneralNominalVersionedMixedCurrentCandidate235.installable
      (current registryEq snapshot rfl selected materialized choice common) cache selected

end Yulang.GeneralNominalVersionedMixedGuardReduction235
