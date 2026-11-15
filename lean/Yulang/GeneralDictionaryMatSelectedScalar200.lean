import Yulang.GeneralDictionaryMatStableScalar200

set_option backward.isDefEq.respectTransparency false

/-! Stability transfers an actual current extension's packet semantics to every
current model. Extension remains explicit; selection alone does not supply it. -/
namespace Yulang.GeneralDictionaryMatSelectedScalar200
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

theorem selected_children (effect : Effect roles)
    (selected : Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core) :
    effect.plan.packet.children = children := by
  have unique := snapshot ▸ registryEq ▸ effect.unique
  cases selected with
  | selected _ chosen _ => exact (chosen.2 _ _ unique.1).2

theorem evidence_of_selected_common_model (effect : Effect roles) (checked : Checked registry)
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
      children dictionaries) :
    (boundary roles).Evidence registry state assignment effect.plan.packet.site.occurrence
      (.node effect.plan.packet.declaration.id dictionaries) := by
  have same := selected_children effect selected registryEq snapshot
  apply GeneralDictionaryMatStableScalar200.evidence_of_common_model effect checked reachable stable
    selected registryEq snapshot choice common variables defined scalars assignment models dictionaries
  rw [same]
  exact childEvidence

end Yulang.GeneralDictionaryMatSelectedScalar200
