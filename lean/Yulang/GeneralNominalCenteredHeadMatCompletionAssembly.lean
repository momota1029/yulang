import Yulang.GeneralNominalCenteredHeadMatCompletionLive

/-! The remaining production obligations are separate from registry transport
and post-install class retention. No live-effect premise is left in assembly. -/
namespace Yulang.GeneralNominalCenteredHeadMatCompletionAssembly
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepBoundary (boundary Local)
open GeneralNominalCenteredHeadMatStepCompletion (SelectedCompletion GeneratedSelectedChildren)
variable {roles : Roles.RoleDecls}

def HeadBaseline (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root focus key children,
    B4TargetV6.Reachable (boundary roles) registry root state →
    Local registry state focus (.selected key children) →
    ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepLocal.ChosenHead registry state focus key model

def PacketAssembly (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root (effect : Effect roles),
    B4TargetV6.Reachable (boundary roles) registry root state →
    effect.registry = registry → effect.snapshot = state.core →
    (∃ model, Models state model ∧ effect.Holds model) →
    ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model

def ChoiceFromCommon (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root (effect : Effect roles) children,
    B4TargetV6.Reachable (boundary roles) registry root state →
    effect.registry = registry → effect.snapshot = state.core →
    Local registry state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id children) →
    (∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model) →
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet

theorem selectedCompletion (baseline : HeadBaseline roles) (assembly : PacketAssembly roles)
    (choice : ChoiceFromCommon roles) : SelectedCompletion roles := by
  intro registry checked state root focus key children reachable selected
  obtain ⟨effect,model,registryEq,snapshot,focusEq,keyEq,childrenEq,valid,chosen⟩ :=
    GeneralNominalCenteredHeadMatStepCompletion.selected_effect_model selected
      (baseline registry checked state root focus key children reachable selected)
  have common := assembly registry checked state root effect reachable registryEq snapshot ⟨model,valid,chosen⟩
  have compatible := choice registry checked state root effect children reachable registryEq snapshot
    (focusEq.symm ▸ keyEq.symm ▸ selected) common
  exact ⟨effect,registryEq,snapshot,focusEq,keyEq,childrenEq,
    (GeneralNominalCenteredHeadMatCompletionLive.extension_iff checked.2 reachable registryEq snapshot).mpr ⟨compatible,common⟩⟩

theorem generatedSelectedChildren (baseline : HeadBaseline roles) (assembly : PacketAssembly roles)
    (choice : ChoiceFromCommon roles) : GeneratedSelectedChildren roles :=
  GeneralNominalCenteredHeadMatStepCompletion.generatedSelectedChildren (selectedCompletion baseline assembly choice)

end Yulang.GeneralNominalCenteredHeadMatCompletionAssembly
