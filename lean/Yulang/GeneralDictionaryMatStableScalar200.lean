import Yulang.GeneralDictionaryMatScalarOutputs200
import Yulang.GeneralNominalCenteredHeadMatCompletionLive

set_option backward.isDefEq.respectTransparency false

/-! Stability transfers an actual current extension's packet semantics to every
current model. Extension remains explicit; selection alone does not supply it. -/
namespace Yulang.GeneralDictionaryMatStableScalar200
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepBoundary (boundary Local)
open GeneralNominalCenteredHeadMatStepKernel (Stable)
open GeneralNominalCenteredHeadMatStepAvailability (Extension)
open GeneralDictionaryVariableRequirements (VariableClauses)
open GeneralDictionaryMatScalarOutputs200 (ScalarRequests)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}

/-- No Frame, recorded membership, or same-assignment Holds premise. The
existential installation compatibility in Extension is not omitted. -/
theorem evidence_of_stable_extension (effect : Effect roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (stable : Stable registry state effect.plan.packet.site.occurrence)
    (selected : Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (extension : Extension state effect)
    (variables : VariableClauses effect.plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
    (scalars : ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration effect.plan.packet.site.occurrence))
    (assignment : Assignment) (models : Models state assignment)
    (dictionaries : List Dictionary)
    (childEvidence : All₂ (fun child dictionary => (boundary roles).Evidence registry state assignment child dictionary)
      effect.plan.packet.children dictionaries) :
    (boundary roles).Evidence registry state assignment effect.plan.packet.site.occurrence
      (.node effect.plan.packet.declaration.id dictionaries) := by
  have committed := GeneralNominalCenteredHeadMatStepAvailability.stable_focus_selected_committed
    reachable stable selected registryEq snapshot extension
  have reg : effect.plan.packet.registry = registry := effect.frame.registry_eq.trans registryEq
  have frame : GeneralNominalCenteredHeadOutputs.Frame effect.plan.packet.registry state.core
      effect.plan.packet.site.occurrence effect.plan.packet.declaration.id effect.plan := by
    rw [reg]
    exact snapshot ▸ registryEq ▸ effect.frame
  rw [← reg] at childEvidence ⊢
  exact GeneralDictionaryMatScalarOutputs200.evidence_of_frame_total effect.plan state frame assignment
    (committed.1 assignment models) variables defined scalars dictionaries childEvidence

/-- Only one jointly valid extension model is supplied, not Holds in the target
assignment. Stability produces the latter. The chosen model may differ. -/
theorem evidence_of_common_model (effect : Effect roles) (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (stable : Stable registry state effect.plan.packet.site.occurrence)
    (selected : Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
    (common : ∃ model, Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model)
    (variables : VariableClauses effect.plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
    (scalars : ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration effect.plan.packet.site.occurrence))
    (assignment : Assignment) (models : Models state assignment)
    (dictionaries : List Dictionary)
    (childEvidence : All₂ (fun child dictionary => (boundary roles).Evidence registry state assignment child dictionary)
      effect.plan.packet.children dictionaries) :
    (boundary roles).Evidence registry state assignment effect.plan.packet.site.occurrence
      (.node effect.plan.packet.declaration.id dictionaries) :=
  evidence_of_stable_extension effect reachable stable selected registryEq snapshot
    ((GeneralNominalCenteredHeadMatCompletionLive.extension_iff checked reachable registryEq snapshot).mpr ⟨choice,common⟩)
    variables defined scalars assignment models dictionaries childEvidence

end Yulang.GeneralDictionaryMatStableScalar200
