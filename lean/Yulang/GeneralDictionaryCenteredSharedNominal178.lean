import Yulang.GeneralDictionaryNominalPairShared178
import Yulang.GeneralDictionaryCenteredNominal178

/-! Current centered nonpoint candidates with arbitrary repeated binder names.
The exact model-indexed residual consists of semantic sharing and extrema;
neither is supplied by existential candidate consistency alone. -/
namespace Yulang.GeneralDictionaryCenteredSharedNominal178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryNominalPairShared178
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem candidate_holds_iff_residual
    (candidate : Candidate registry state focus key children plan)
    (shape : SharedShape plan.packet.context plan.packet.declaration)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(shape.lower,shape.upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model ↔
    GeneralNominalSharedCaptureFacts.Coherent model (plan.packet.context.state.base.source shape.lower)
      shape.left.declaration.name shape.names ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration
        (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds))) := by
  have source : GeneralNominalState.Models plan.packet.context.state model := by
    rw [candidate.context_eq]; exact valid.1.1
  have ordered := GeneralDictionaryCenteredScalarIntervals177.candidate_ordered candidate model valid
    [(shape.lower,shape.upper)] located (shape.lower,shape.upper) (by simp)
  have same := Option.some.inj (candidate.located.symm.trans located)
  change BranchModels _ _ _ _ _ _ _ ↔ _
  rw [same,branch_models_iff_shared_residual plan.packet.context plan.packet.registry plan.packet.site.occurrence
    plan.packet.declaration plan.packet.checked shape terminal outputs model]
  exact ⟨fun h => h.2.2,fun h => ⟨source,ordered,h⟩⟩

 theorem candidate_evidence
    (candidate : Candidate registry state focus key children plan)
    (shape : SharedShape plan.packet.context plan.packet.declaration)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(shape.lower,shape.upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (coherent : GeneralNominalSharedCaptureFacts.Coherent model (plan.packet.context.state.base.source shape.lower)
      shape.left.declaration.name shape.names)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration
        (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds)))) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have holds := (candidate_holds_iff_residual candidate shape located terminal outputs model valid).mpr ⟨coherent,merges⟩
  have inst := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model holds
  rw [GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal] at inst
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr inst

end Yulang.GeneralDictionaryCenteredSharedNominal178
