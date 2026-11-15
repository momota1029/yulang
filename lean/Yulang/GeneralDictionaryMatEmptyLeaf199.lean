import Yulang.GeneralNominalCenteredHeadMatStepBoundary
import Yulang.GeneralDictionaryLinearLeaf

set_option backward.isDefEq.respectTransparency false

/-! Genuine total-packet to recursive source evidence for the empty-request leaf
fragment. No old packet Models or BranchModels is a premise. The syntactic
no-requirements/no-request restrictions are essential: the multi-tag witness in
MatGuardWitness199 refutes dropping materialization compatibility in general. -/
namespace Yulang.GeneralDictionaryMatEmptyLeaf199
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} (plan : Plan roles)

theorem schema_empty
    (terminal : plan.packet.declaration.requirements = [])
    (unnamed : plan.packet.site.occurrence.demand.outputs = []) :
    generated plan.packet.registry plan.packet.context plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bounds = {} :=
  GeneralDictionaryLinearLeaf.generated_empty plan.packet.context plan.packet.registry
    plan.packet.site.occurrence plan.packet.declaration plan.packet.checked terminal unnamed plan.packet.bounds

theorem branch_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (terminal : plan.packet.declaration.requirements = [])
    (unnamed : plan.packet.site.occurrence.demand.outputs = []) :
    BranchModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bounds assignment := by
  refine ⟨GeneralNominalCenteredHeadMatStepPackets.private_models holds,holds.2.1.2.1,?_⟩
  rw [schema_empty plan terminal unnamed]
  exact GeneralNominalMaterialization.empty_models ..

theorem instance_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (terminal : plan.packet.declaration.requirements = [])
    (unnamed : plan.packet.site.occurrence.demand.outputs = [])
    (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
    (role : plan.packet.declaration.role = plan.packet.site.occurrence.demand.role)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds)
    (finished : Finished (report plan.packet.context plan.packet.declaration plan.packet.bounds))
    (metadata : Metadata plan.packet.registry plan.packet.context) :
    GeneralDictionaryRecursiveEvidence.Instance plan.packet.registry plan.packet.context assignment
      plan.packet.site.occurrence plan.packet.declaration.id [] := by
  refine ⟨plan.packet.declaration,visible,plan.packet.checked,rfl,role,plan.packet.bounds,
    located,finished,⟨?_,?_⟩,?_,metadata,branch_of_total plan assignment holds terminal unnamed⟩
  · intro output member
    rw [unnamed] at member
    cases member
  · rw [schema_empty plan terminal unnamed]
  · exact (GeneralDictionaryLinearLeaf.children_empty plan.packet.context plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked terminal _).symm

theorem evidence_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (terminal : plan.packet.declaration.requirements = [])
    (unnamed : plan.packet.site.occurrence.demand.outputs = [])
    (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
    (role : plan.packet.declaration.role = plan.packet.site.occurrence.demand.role)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds)
    (finished : Finished (report plan.packet.context plan.packet.declaration plan.packet.bounds))
    (metadata : Metadata plan.packet.registry plan.packet.context) :
    GeneralDictionaryRecursiveEvidence.Evidence plan.packet.registry plan.packet.context assignment
      plan.packet.site.occurrence (.node plan.packet.declaration.id []) :=
  (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff ..).mpr
    (instance_of_total plan assignment holds terminal unnamed visible role located finished metadata)

/-- Frame provenance discharges the inspection and registry premises, while the
model-indexed semantics comes solely from the actual total journal packet. -/
theorem evidence_of_frame_total (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (framed : GeneralNominalCenteredHeadOutputs.Frame plan.packet.registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (terminal : plan.packet.declaration.requirements = [])
    (unnamed : plan.packet.site.occurrence.demand.outputs = []) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
      plan.packet.site.occurrence (.node plan.packet.declaration.id []) := by
  have prepared : GeneralNominalCenteredHeadCandidates.Prepared plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration := by
    rw [framed.context_eq]
    exact framed.prepared
  obtain ⟨metadata,_,_,bounds,found,finished,_⟩ := prepared
  have equal := Option.some.inj (found.symm.trans framed.located)
  subst bounds
  change GeneralDictionaryRecursiveEvidence.Evidence plan.packet.registry
    state.core.erased.current.context assignment plan.packet.site.occurrence _
  rw [← framed.context_eq]
  exact evidence_of_total plan assignment holds terminal unnamed framed.visible framed.role_eq
    framed.located finished metadata

end Yulang.GeneralDictionaryMatEmptyLeaf199
