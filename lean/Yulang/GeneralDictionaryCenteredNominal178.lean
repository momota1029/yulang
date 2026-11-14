import Yulang.GeneralDictionaryNominalPair178
import Yulang.GeneralNominalMergeResidual178
import Yulang.GeneralDictionaryCenteredScalarIntervals177

/-! Nonpoint nominal candidates at the unchanged centered boundary. Current
center sandwiches derive endpoint order. Only the actual capture extrema in
the supplied assignment remain; a candidate's existential model is not reused. -/
namespace Yulang.GeneralDictionaryCenteredNominal178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryNominalPair178

variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

/-- An exact residual for the branch of a current terminal nominal-pair
candidate. Reachability, stability and journal membership are not assumed. -/
theorem candidate_holds_iff_merges
    (candidate : Candidate registry state focus key children plan)
    (shape : Shape plan.packet.context plan.packet.declaration)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(shape.lower,shape.upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model ↔ PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration
        (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds))) := by
  have ordered := GeneralDictionaryCenteredScalarIntervals177.candidate_ordered candidate model valid
    [(shape.lower,shape.upper)] located
  have same := Option.some.inj (candidate.located.symm.trans located)
  change BranchModels _ _ _ _ _ _ _ ↔ _
  rw [same]
  exact branch_models_iff_merges plan.packet.context plan.packet.registry plan.packet.site.occurrence
    plan.packet.declaration plan.packet.checked shape terminal outputs model
    (by rw [candidate.context_eq]; exact valid.1.1) (ordered (shape.lower,shape.upper) (by simp))

/-- The residual can equivalently be stated as semantic lower/upper extrema,
without requiring a complete private-state or branch premise. -/
theorem candidate_holds_iff_extrema
    (candidate : Candidate registry state focus key children plan)
    (shape : Shape plan.packet.context plan.packet.declaration)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(shape.lower,shape.upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model ↔ GeneralNominalMergeResidual178.CaptureExtrema
      plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity
      plan.packet.declaration (bindings plan.packet.context.state
        (report plan.packet.context plan.packet.declaration plan.packet.bounds)) model := by
  rw [candidate_holds_iff_merges candidate shape located terminal outputs model valid,
    GeneralNominalMergeResidual178.merges_iff_extrema]

/-- A conditional leaf producer for the actual current candidate, not an
installation rule or a theorem for all nominal shapes. -/
theorem candidate_evidence
    (candidate : Candidate registry state focus key children plan)
    (shape : Shape plan.packet.context plan.packet.declaration)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(shape.lower,shape.upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (extrema : GeneralNominalMergeResidual178.CaptureExtrema
      plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity
      plan.packet.declaration (bindings plan.packet.context.state
        (report plan.packet.context plan.packet.declaration plan.packet.bounds)) model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have holds := (candidate_holds_iff_extrema candidate shape located terminal outputs model valid).mpr extrema
  have inst := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model holds
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at inst
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr inst

/-- Every supplied child dictionary list is empty for this terminal producer;
this is the EvidenceNode-shaped conclusion for the stated fragment only. -/
theorem candidate_evidence_node
    (candidate : Candidate registry state focus key children plan)
    (shape : Shape plan.packet.context plan.packet.declaration)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(shape.lower,shape.upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (extrema : GeneralNominalMergeResidual178.CaptureExtrema
      plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity
      plan.packet.declaration (bindings plan.packet.context.state
        (report plan.packet.context plan.packet.declaration plan.packet.bounds)) model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key dictionaries) := by
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at given
  cases given
  exact candidate_evidence candidate shape located terminal outputs model valid extrema

end Yulang.GeneralDictionaryCenteredNominal178
