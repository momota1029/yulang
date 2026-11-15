import Yulang.GeneralDictionaryMatSelectedScalar200
import Yulang.GeneralDictionaryMatInputAssembly201

set_option backward.isDefEq.respectTransparency false

/-! Stability transfers an actual current extension's packet semantics to every
current model. Extension remains explicit; selection alone does not supply it. -/
namespace Yulang.GeneralDictionaryMatSelectedInputs201
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

theorem evidence_of_selected_common_head (effect : Effect roles) (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (stable : Stable registry state effect.plan.packet.site.occurrence)
    (selected : Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
    (common : ∃ model, Models state model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels effect.plan.packet.registry effect.plan.packet.context
        effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.bounds model ∧ effect.Holds model)
    (restricted : GeneralDictionaryMatInputVariables201.InputVariableClauses effect.plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
    (scalars : ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration effect.plan.packet.site.occurrence))
    (assignment : Assignment) (models : Models state assignment)
    (dictionaries : List Dictionary)
    (childEvidence : All₂ (fun child dictionary => (boundary roles).Evidence registry state assignment child dictionary)
      children dictionaries) :
    (boundary roles).Evidence registry state assignment effect.plan.packet.site.occurrence
      (.node effect.plan.packet.declaration.id dictionaries) := by
  have full : ∃ model, Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
    obtain ⟨model,valid,head,chosen⟩ := common
    exact ⟨model,valid,GeneralDictionaryMatInputAssembly201.holds_of_head_class effect.plan effect.snapshot
      effect.frame.raw_recorded model head chosen.1 chosen.2 restricted,chosen⟩
  exact GeneralDictionaryMatSelectedScalar200.evidence_of_selected_common_model effect checked reachable stable
    selected registryEq snapshot choice full (GeneralDictionaryMatInputVariables201.variable_clauses restricted)
    defined scalars assignment models dictionaries childEvidence

end Yulang.GeneralDictionaryMatSelectedInputs201
