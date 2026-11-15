import Yulang.GeneralDictionaryAllocV7InputBridge201
import Yulang.GeneralDictionaryMatTreeHead201

namespace Yulang.GeneralDictionaryAllocV7TreeEvidence201
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryMatInputVariables201
open GeneralDictionaryMatScalarOutputs200 (ScalarRequests)
open GeneralDictionaryMatTreeHead201 (HeadTree)
open GeneralDictionaryAllocV7InputBridge201 (boundary compiled)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)
variable {roles : Roles.RoleDecls} {value : Registry} {state : State roles}

/-- Same-model HeadModels is now proved from the finite-tree shape. Only the
joint journal/effect witness remains, not packet Holds or head validity. -/
theorem evidence_of_selected_tree (effect : Effect roles) (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (stable : (boundary roles).Stable value state effect.plan.packet.site.occurrence)
    (selected : GeneralNominalCenteredHeadAllocV7Boundary.Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = compiled value) (snapshot : effect.snapshot = state.core)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
    (shape : HeadTree effect.plan)
    (common : ∃ model, Models state model ∧ effect.Holds model)
    (restricted : InputVariableClauses effect.plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
    (scalars : ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration effect.plan.packet.site.occurrence))
    (assignment : Assignment) (models : Models state assignment)
    (dictionaries : List Dictionary)
    (childEvidence : All₂ (fun child dictionary => (boundary roles).Evidence value state assignment child dictionary)
      children dictionaries) :
    (boundary roles).Evidence value state assignment effect.plan.packet.site.occurrence
      (.node effect.plan.packet.declaration.id dictionaries) := by
  apply GeneralDictionaryAllocV7InputBridge201.evidence_of_selected_common_head effect checked reachable stable
    selected registryEq snapshot choice _ restricted defined scalars assignment models dictionaries childEvidence
  obtain ⟨model,valid,effects⟩ := common
  exact ⟨model,valid,GeneralDictionaryMatTreeHead201.current_head_models effect.plan shape state
    (snapshot ▸ effect.frame) model valid,effects⟩

end Yulang.GeneralDictionaryAllocV7TreeEvidence201
