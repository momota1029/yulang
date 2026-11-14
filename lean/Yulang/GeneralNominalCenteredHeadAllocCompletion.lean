import Yulang.GeneralNominalCenteredHeadAllocExecutor
import Yulang.GeneralNominalCenteredHeadAllocOutputModels

/-! Production obligations are scoped to executions of the repaired boundary.
An assumption about every uncompiled registry would retain the old collision.
The common-model equivalence already includes the entire live effect ledger. -/
namespace Yulang.GeneralNominalCenteredHeadAllocCompletion
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadAllocBoundary
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCenteredHeadMatStepAvailability (Extension)
variable {roles : Roles.RoleDecls}

def HeadBaseline (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root focus key children,
    B4TargetV6.Reachable (boundary roles) value root state →
    Local value state focus (.selected key children) →
    ∃ model, Models state model ∧
      GeneralNominalCenteredHeadMatStepLocal.ChosenHead (registry value) state focus key model

def PacketAssembly (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root (effect : Effect roles),
    B4TargetV6.Reachable (boundary roles) value root state →
    effect.registry = registry value → effect.snapshot = state.core →
    (∃ model, Models state model ∧ effect.Holds model) →
    ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model

def ChoiceFromCommon (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root (effect : Effect roles) children,
    B4TargetV6.Reachable (boundary roles) value root state →
    effect.registry = registry value → effect.snapshot = state.core →
    Local value state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id children) →
    (∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model) →
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet

def SelectedCompletion (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root focus key children,
    B4TargetV6.Reachable (boundary roles) value root state →
    Local value state focus (.selected key children) →
    ∃ effect : Effect roles, effect.registry = registry value ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children ∧ Extension state effect

def GeneratedSelectedChildren (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root focus key children,
    B4TargetV6.Reachable (boundary roles) value root state → Stable value state focus →
    GeneralNominalSaturationState.Generated state.core.erased.current root focus →
    Local value state focus (.selected key children) →
    ∀ child ∈ children, GeneralNominalSaturationState.Generated state.core.erased.current root child

theorem extension_iff (checked : (boundary roles).Checked value)
    (reachable : B4TargetV6.Reachable (boundary roles) value root state)
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) :
    Extension state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
      ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model :=
  GeneralNominalCenteredHeadMatCompletionLive.extension_iff (checked_compiled checked).2
    (reachable_compiled reachable) registryEq snapshot

theorem selected_installable_iff
    (reachable : B4TargetV6.Reachable (boundary roles) value root state)
    (selected : Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) :
    GeneralNominalCenteredHeadMatStepKernel.Installable (registry value) state effect ↔ Extension state effect :=
  GeneralNominalCenteredHeadMatStepAvailability.selected_installable_iff (reachable_compiled reachable)
    (local_iff.mp selected) registryEq snapshot

theorem selectedCompletion (baseline : HeadBaseline roles) (assembly : PacketAssembly roles)
    (choice : ChoiceFromCommon roles) : SelectedCompletion roles := by
  intro value checked state root focus key children reachable selected
  obtain ⟨effect,model,registryEq,snapshot,focusEq,keyEq,childrenEq,valid,chosen⟩ :=
    GeneralNominalCenteredHeadMatStepCompletion.selected_effect_model (local_iff.mp selected)
      (baseline value checked state root focus key children reachable selected)
  have common := assembly value checked state root effect reachable registryEq snapshot ⟨model,valid,chosen⟩
  have compatible := choice value checked state root effect children reachable registryEq snapshot
    (focusEq.symm ▸ keyEq.symm ▸ selected) common
  exact ⟨effect,registryEq,snapshot,focusEq,keyEq,childrenEq,
    (extension_iff checked reachable registryEq snapshot).mpr ⟨compatible,common⟩⟩

theorem generated_of_completion (completion : SelectedCompletion roles) : GeneratedSelectedChildren roles := by
  intro value checked state root focus key children reached stable generated selected child member
  obtain ⟨effect,registryEq,snapshot,focusEq,keyEq,childrenEq,extension⟩ :=
    completion value checked state root focus key children reached selected
  have done := GeneralNominalCenteredHeadMatStepAvailability.stable_focus_selected_committed
    (reachable_compiled reached) (focusEq.symm ▸ stable)
    (local_iff.mp (focusEq.symm ▸ keyEq.symm ▸ selected)) registryEq snapshot extension
  exact .child generated (focusEq ▸ done.2 child (childrenEq.symm ▸ member))

theorem generatedSelectedChildren (baseline : HeadBaseline roles) (assembly : PacketAssembly roles)
    (choice : ChoiceFromCommon roles) : GeneratedSelectedChildren roles :=
  generated_of_completion (selectedCompletion baseline assembly choice)

end Yulang.GeneralNominalCenteredHeadAllocCompletion
