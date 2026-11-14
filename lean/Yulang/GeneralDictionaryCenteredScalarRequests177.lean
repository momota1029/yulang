import Yulang.GeneralDictionaryCenteredScalarIntervals177
import Yulang.GeneralDictionaryObservedClosedRequests

/-! Closed observed materialization requests allow nonterminal scalar interval
candidates. Child evidence is retained in its actual order and multiplicity. -/
namespace Yulang.GeneralDictionaryCenteredScalarRequests177
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryScalarIntervalInspection
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

theorem candidate_holds
    (candidate : Candidate registry state focus key children plan) (bases : List Inference.Base)
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = bases.map .scalar)
    (observed : GeneralDictionaryObservedClosedRequests.Observed plan.packet.context.state
      plan.packet.context.interpretation (GeneralNominalMaterialization.requests
        plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
        plan.packet.declaration plan.packet.checked plan.packet.bindings))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model := by
  obtain ⟨metadata,linked,fresh,bounds,located,finished,ready,consistent⟩ := candidate.prepared
  have fi : Finished (inspectMany plan.packet.context.state (bases.map .scalar) bounds (fun _ => none) 0) := by
    simpa only [report,query,Finished] using finished
  obtain ⟨entries,qe,pe,obs⟩ := GeneralDictionaryCenteredScalarIntervals177.recover_entries plan.packet.context.state bases bounds 0 fi
  let shape : Shape plan.packet.context plan.packet.site.occurrence plan.packet.declaration :=
    ⟨by simpa only [candidate.occurrence_eq] using candidate.role,entries,obs,inputs,
      query.trans qe.symm,by rw [pe]; exact located,ready.1⟩
  have ordered := GeneralDictionaryCenteredScalarIntervals177.candidate_ordered candidate model valid bounds located
  have privateValid := private_models plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration shape model (by rw [candidate.context_eq]; exact valid.1.1)
    (by change ∀ pair ∈ intervals entries, _; rw [pe]; exact ordered)
  have packetBounds : plan.packet.bounds = bounds := Option.some.inj (candidate.located.symm.trans located)
  have converted : GeneralDictionaryObservedClosedRequests.Observed plan.packet.context.state
      plan.packet.context.interpretation (GeneralNominalMaterialization.requests
        plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
        plan.packet.declaration plan.packet.checked
        (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration (intervals entries)))) := by
    simpa only [GeneralNominalSaturationState.Packet.bindings,packetBounds,pe] using observed
  have branch : BranchModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked (intervals entries) model := by
    refine ⟨privateValid.1,privateValid.2,?_⟩
    exact GeneralDictionaryObservedClosedRequests.generated_models _ _ _ converted _ _ _ model
      (by rw [candidate.context_eq]; exact valid.1.1)
  change BranchModels _ _ _ _ _ _ _
  rw [packetBounds,← pe]
  exact branch

theorem candidate_instance
    (candidate : Candidate registry state focus key children plan) (bases : List Inference.Base)
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = bases.map .scalar)
    (observed : GeneralDictionaryObservedClosedRequests.Observed plan.packet.context.state
      plan.packet.context.interpretation (GeneralNominalMaterialization.requests
        plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
        plan.packet.declaration plan.packet.checked plan.packet.bindings))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.erased.current.context model focus key children :=
  GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model
    (candidate_holds candidate bases inputs query observed model valid)

theorem candidate_evidence
    (candidate : Candidate registry state focus key children plan) (bases : List Inference.Base)
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = bases.map .scalar)
    (observed : GeneralDictionaryObservedClosedRequests.Observed plan.packet.context.state
      plan.packet.context.interpretation (GeneralNominalMaterialization.requests
        plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
        plan.packet.declaration plan.packet.checked plan.packet.bindings))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.erased.current.context model focus key
    children dictionaries (candidate_instance candidate bases inputs query observed model valid) given

end Yulang.GeneralDictionaryCenteredScalarRequests177
