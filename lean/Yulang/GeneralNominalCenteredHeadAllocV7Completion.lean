import Yulang.GeneralNominalCenteredHeadAllocV7Executor
import Yulang.GeneralNominalCenteredHeadAllocOutputModels

/-! Production obligations are scoped to executions of the repaired boundary.
An assumption about every uncompiled registry would retain the old collision.
The common-model equivalence already includes the entire live effect ledger. -/
namespace Yulang.GeneralNominalCenteredHeadAllocV7Completion
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadAllocV7Boundary
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCenteredHeadMatStepAvailability (Extension)
variable {roles : Roles.RoleDecls}

def HeadBaseline (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root focus key children,
    B4TargetV7.Reachable (boundary roles) value root state →
    Local value state focus (.selected key children) →
    ∃ model, Models state model ∧
      GeneralNominalCenteredHeadMatStepLocal.ChosenHead (registry value) state focus key model

def PacketAssembly (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root (effect : Effect roles),
    B4TargetV7.Reachable (boundary roles) value root state →
    effect.registry = registry value → effect.snapshot = state.core →
    (∃ model, Models state model ∧ effect.Holds model) →
    ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model

def ChoiceFromCommon (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root (effect : Effect roles) children,
    B4TargetV7.Reachable (boundary roles) value root state →
    effect.registry = registry value → effect.snapshot = state.core →
    Local value state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id children) →
    (∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model) →
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet

def SelectedCompletion (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root focus key children,
    B4TargetV7.Reachable (boundary roles) value root state →
    Local value state focus (.selected key children) →
    ∃ effect : Effect roles, effect.registry = registry value ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children ∧ Extension state effect

end Yulang.GeneralNominalCenteredHeadAllocV7Completion
