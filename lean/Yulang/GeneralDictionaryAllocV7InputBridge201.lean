import Yulang.GeneralDictionaryMatSelectedInputs201
import Yulang.GeneralNominalCenteredHeadAllocV7Boundary

/-! Transport the restricted, same-model assembly to the owner's allocation
compiler and V7 selected-only boundary. No global completion is assumed. -/
namespace Yulang.GeneralDictionaryAllocV7InputBridge201
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryMatInputVariables201
open GeneralDictionaryMatScalarOutputs200 (ScalarRequests)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)
variable {roles : Roles.RoleDecls} {value : Registry} {state : State roles}

abbrev compiled := GeneralNominalCenteredHeadAllocEncoding.registry
abbrev boundary := GeneralNominalCenteredHeadAllocV7Boundary.boundary

theorem restricted_compiled (declaration : Declaration) :
    InputVariableClauses (GeneralNominalCenteredHeadAllocEncoding.declaration declaration) ↔
      InputVariableClauses declaration := by
  constructor
  · intro restricted clause member
    have result := restricted (GeneralNominalCenteredHeadAllocEncoding.clause clause)
      (List.mem_map.mpr ⟨clause,member,rfl⟩)
    refine ⟨List.map_eq_nil_iff.mp result.1,?_⟩
    intro pattern present
    obtain ⟨name,equal,input,notOutput⟩ := result.2 pattern present
    exact ⟨name,equal,input,by simpa using notOutput⟩
  · intro restricted next member
    obtain ⟨clause,present,rfl⟩ := List.mem_map.mp member
    have result := restricted clause present
    refine ⟨by simp [GeneralNominalCenteredHeadAllocEncoding.clause,result.1],?_⟩
    intro pattern member
    obtain ⟨name,equal,input,notOutput⟩ := result.2 pattern member
    exact ⟨name,equal,input,by simpa using notOutput⟩

theorem root_requests_compiled (declaration : Declaration) (root : Occurrence roles) :
    GeneralNominalMaterialization.rootRequests (GeneralNominalCenteredHeadAllocEncoding.declaration declaration) root =
    GeneralNominalMaterialization.rootRequests declaration root := rfl

theorem selected_kernel
    (selected : GeneralNominalCenteredHeadAllocV7Boundary.Local value state focus (.selected key children)) :
    GeneralNominalCenteredHeadMatStepBoundary.Local (compiled value) state focus (.selected key children) :=
  GeneralNominalCenteredHeadAllocBoundary.local_iff.mp (B4TargetV7.selected_iff.mp selected).1

/-- The common witness may differ from the target assignment. Stability transfers
its assembled packet semantics; exact V7 children and their multiplicity survive. -/
theorem evidence_of_selected_common_head (effect : Effect roles) (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (stable : (boundary roles).Stable value state effect.plan.packet.site.occurrence)
    (selected : GeneralNominalCenteredHeadAllocV7Boundary.Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = compiled value) (snapshot : effect.snapshot = state.core)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
    (common : ∃ model, Models state model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels effect.plan.packet.registry effect.plan.packet.context
        effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.bounds model ∧ effect.Holds model)
    (restricted : InputVariableClauses effect.plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
    (scalars : ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration effect.plan.packet.site.occurrence))
    (assignment : Assignment) (models : Models state assignment)
    (dictionaries : List Dictionary)
    (childEvidence : All₂ (fun child dictionary => (boundary roles).Evidence value state assignment child dictionary)
      children dictionaries) :
    (boundary roles).Evidence value state assignment effect.plan.packet.site.occurrence
      (.node effect.plan.packet.declaration.id dictionaries) :=
  GeneralDictionaryMatSelectedInputs201.evidence_of_selected_common_head effect
    (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2
    (GeneralNominalCenteredHeadAllocBoundary.reachable_compiled reachable) stable
    (selected_kernel selected) registryEq snapshot choice common restricted defined scalars
    assignment models dictionaries childEvidence

end Yulang.GeneralDictionaryAllocV7InputBridge201
