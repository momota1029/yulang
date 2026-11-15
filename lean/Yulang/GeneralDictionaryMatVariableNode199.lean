import Yulang.GeneralDictionaryMatEmptyLeaf199
import Yulang.GeneralDictionaryVariableRequirements

set_option backward.isDefEq.respectTransparency false

/-! Nonterminal request-empty bridge over the actual total journal. Child demands
and evidence keep their complete canonical list and multiplicity. The restriction
is on source request syntax, not old packet semantics or assumed parent evidence. -/
namespace Yulang.GeneralDictionaryMatVariableNode199
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVariableRequirements (VariableClauses)
open CommonRoleOutermostResolver (All₂ Dictionary)
variable {roles : Roles.RoleDecls} (plan : Plan roles)

theorem branch_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (variables : VariableClauses plan.packet.declaration)
    (unnamed : plan.packet.site.occurrence.demand.outputs = []) :
    BranchModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bounds assignment := by
  refine ⟨GeneralNominalCenteredHeadMatStepPackets.private_models holds,holds.2.1.2.1,?_⟩
  rw [GeneralDictionaryVariableRequirements.generated_empty _ _ _ _ _ _ unnamed variables]
  exact GeneralNominalMaterialization.empty_models ..

theorem instance_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (variables : VariableClauses plan.packet.declaration)
    (unnamed : plan.packet.site.occurrence.demand.outputs = [])
    (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
    (role : plan.packet.declaration.role = plan.packet.site.occurrence.demand.role)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds)
    (finished : Finished (report plan.packet.context plan.packet.declaration plan.packet.bounds))
    (metadata : Metadata plan.packet.registry plan.packet.context) :
    GeneralDictionaryRecursiveEvidence.Instance plan.packet.registry plan.packet.context assignment
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
  refine ⟨plan.packet.declaration,visible,plan.packet.checked,rfl,role,plan.packet.bounds,
    located,finished,⟨?_,?_⟩,rfl,metadata,branch_of_total plan assignment holds variables unnamed⟩
  · intro output member
    rw [unnamed] at member
    cases member
  · rw [GeneralDictionaryVariableRequirements.generated_empty _ _ _ _ _ _ unnamed variables]

theorem evidence_of_frame_total (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (framed : GeneralNominalCenteredHeadOutputs.Frame plan.packet.registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (variables : VariableClauses plan.packet.declaration)
    (unnamed : plan.packet.site.occurrence.demand.outputs = [])
    (dictionaries : List Dictionary)
    (children : All₂ (fun child dictionary =>
      (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
        child dictionary) plan.packet.children dictionaries) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
      plan.packet.site.occurrence (.node plan.packet.declaration.id dictionaries) := by
  have prepared : GeneralNominalCenteredHeadCandidates.Prepared plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration := by
    rw [framed.context_eq]
    exact framed.prepared
  obtain ⟨metadata,_,_,bounds,found,finished,_⟩ := prepared
  have equal := Option.some.inj (found.symm.trans framed.located)
  subst bounds
  change GeneralDictionaryRecursiveEvidence.Evidence plan.packet.registry
    state.core.erased.current.context assignment plan.packet.site.occurrence _
  change All₂ (GeneralDictionaryRecursiveEvidence.Evidence plan.packet.registry
    state.core.erased.current.context assignment) plan.packet.children dictionaries at children
  rw [← framed.context_eq] at children ⊢
  exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
    (instance_of_total plan assignment holds variables unnamed framed.visible framed.role_eq
      framed.located finished metadata) children

/-- Recording and current journal Models supply actual total Holds in the very
same assignment used for the children. No existential candidate model is swapped in. -/
theorem evidence_of_recorded (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (framed : GeneralNominalCenteredHeadOutputs.Frame plan.packet.registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (recorded : plan ∈ state.core.plans)
    (assignment : Assignment) (models : GeneralNominalCenteredHeadMatStepJournal.Models state assignment)
    (variables : VariableClauses plan.packet.declaration)
    (unnamed : plan.packet.site.occurrence.demand.outputs = [])
    (dictionaries : List Dictionary)
    (children : All₂ (fun child dictionary =>
      (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
        child dictionary) plan.packet.children dictionaries) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
      plan.packet.site.occurrence (.node plan.packet.declaration.id dictionaries) :=
  evidence_of_frame_total plan state framed assignment (models.2.2.2.2.1 plan recorded)
    variables unnamed dictionaries children

end Yulang.GeneralDictionaryMatVariableNode199
