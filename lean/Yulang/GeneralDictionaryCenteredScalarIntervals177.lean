import Yulang.GeneralDictionaryCenteredRootScalar177
import Yulang.GeneralDictionaryScalarIntervalInspection

/-! Recover scalar interval evidence from actual centered sites, without
point or reachability hypotheses. -/
namespace Yulang.GeneralDictionaryCenteredScalarIntervals177
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryScalarIntervalInspection

private theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished,Report.append,List.append_eq_nil_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩; exact ⟨⟨a,c,e⟩,b,d,f⟩
  · rintro ⟨⟨a,c,e⟩,b,d,f⟩; exact ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩

 theorem scalar_finished (state : GeneralNominalState.State)
    (bounds : GeneralNominalInspection.Bounds state) (base : Inference.Base)
    (origin : Option Origin)
    (finished : Finished (inspect state (.scalar base) bounds origin)) :
    state.nominals bounds.1 = none ∧ state.view.heads bounds.1 = .scalar base := by
  cases hn : state.nominals bounds.1 with
  | some value => simp [inspect,hn,Report.visit,Finished] at finished
  | none =>
    refine ⟨rfl,?_⟩
    cases hh : state.view.heads bounds.1 <;>
      simp [inspect,hn,hh,Report.visit,Finished,block] at finished
    rename_i actual
    split at finished
    next h => simp [h]
    next h => simp at finished

theorem recover_entries (state : GeneralNominalState.State)
    (bases : List Inference.Base) (bounds : List (GeneralNominalInspection.Bounds state))
    (index : Nat)
    (finished : Finished (inspectMany state (bases.map .scalar) bounds (fun _ => none) index)) :
    ∃ entries : List (GeneralNominalInspection.Bounds state × Inference.Base),
      queries entries = bases.map .scalar ∧ intervals entries = bounds ∧ Observed state entries := by
  induction bases generalizing bounds index with
  | nil =>
    cases bounds with
    | nil => exact ⟨[],rfl,rfl,by simp [Observed]⟩
    | cons b rest => simp [inspectMany,Finished] at finished
  | cons base bases ih =>
    cases bounds with
    | nil => simp [inspectMany,Finished] at finished
    | cons b rest =>
      simp only [List.map_cons,inspectMany] at finished
      have parts := (finished_append _ _).mp finished
      have observed := scalar_finished state b base none parts.1
      obtain ⟨entries,queriesEq,pointsEq,observedTail⟩ := ih rest (index+1) parts.2
      refine ⟨(b,base)::entries,?_,?_,?_⟩
      · exact congrArg (List.cons (.scalar base)) queriesEq
      · exact congrArg (List.cons b) pointsEq
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact observed
        · exact observedTail entry member

variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

theorem candidate_ordered
    (candidate : Candidate registry state focus key children plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (bounds : List (GeneralNominalInspection.Bounds plan.packet.context.state))
    (located : arguments plan.packet.context plan.packet.site.occurrence = some bounds) :
    ∀ pair ∈ bounds, CommonNominalFullCarrier.Subtype
      (model (plan.packet.context.state.base.source pair.1)).1
      (model (plan.packet.context.state.base.source pair.2)).1 := by
  have center := valid.2.1 plan.input candidate.centered_recorded
  intro pair member
  have same := GeneralDictionaryReachableRootIntervals.locate_sources plan.packet.context.state.base
    (List.ofFn plan.packet.site.occurrence.demand.arguments) bounds located
  have present : (plan.packet.context.state.base.source pair.1,plan.packet.context.state.base.source pair.2) ∈
      List.ofFn plan.packet.site.occurrence.demand.arguments := by
    rw [←same]
    exact List.mem_map.mpr ⟨pair,member,rfl⟩
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp present
  have all : ∀ i, CommonNominalFullCarrier.Subtype
      (model (plan.input.occurrence.demand.arguments i).1).1
      (model (plan.input.occurrence.demand.arguments i).2).1 := by
    intro i
    exact CommonNominalFullCarrier.subtype_trans (center i).1 (center i).2
  rw [plan.input_exact] at all
  simpa only [equal] using all index

theorem candidate_holds
    (candidate : Candidate registry state focus key children plan) (bases : List Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = bases.map .scalar)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model := by
  obtain ⟨metadata,linked,fresh,bounds,located,finished,ready,consistent⟩ := candidate.prepared
  have fi : Finished (inspectMany plan.packet.context.state (bases.map .scalar) bounds (fun _ => none) 0) := by
    simpa only [report,query,Finished] using finished
  obtain ⟨entries,qe,pe,obs⟩ := recover_entries plan.packet.context.state bases bounds 0 fi
  let shape : Shape plan.packet.context plan.packet.site.occurrence plan.packet.declaration :=
    ⟨by simpa only [candidate.occurrence_eq] using candidate.role,entries,obs,inputs,
      query.trans qe.symm,by rw [pe]; exact located,by intro out member; rw [outputs] at member; cases member⟩
  have ordered := candidate_ordered candidate model valid bounds located
  have privateValid := private_models plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration shape model (by rw [candidate.context_eq]; exact valid.1.1)
    (by change ∀ pair ∈ intervals entries, _; rw [pe]; exact ordered)
  have branch : BranchModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked (intervals entries) model := by
    refine ⟨privateValid.1,privateValid.2,?_⟩
    rw [GeneralDictionaryLinearLeaf.generated_empty _ _ _ _ _ terminal outputs]
    exact GeneralNominalMaterialization.empty_models ..
  have packetBounds : plan.packet.bounds = bounds := Option.some.inj (candidate.located.symm.trans located)
  change BranchModels _ _ _ _ _ _ _
  rw [packetBounds,← pe]
  exact branch

theorem candidate_evidence
    (candidate : Candidate registry state focus key children plan) (bases : List Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = bases.map .scalar)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have holds := candidate_holds candidate bases terminal outputs inputs query model valid
  have instanceRule := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model holds
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at instanceRule
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr instanceRule

end Yulang.GeneralDictionaryCenteredScalarIntervals177
