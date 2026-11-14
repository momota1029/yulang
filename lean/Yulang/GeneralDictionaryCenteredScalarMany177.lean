import Yulang.GeneralDictionaryCenteredRootScalar177
import Yulang.GeneralDictionaryMultiScalarInspection

/-! Recover all scalar observations from successful point-root inspection,
including zero or repeated scalar arguments. -/
namespace Yulang.GeneralDictionaryCenteredScalarMany177
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryMultiScalarInspection

private theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished,Report.append,List.append_eq_nil_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩; exact ⟨⟨a,c,e⟩,b,d,f⟩
  · rintro ⟨⟨a,c,e⟩,b,d,f⟩; exact ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩

theorem recover_entries (state : GeneralNominalState.State)
    (bases : List Inference.Base) (bounds : List (GeneralNominalInspection.Bounds state))
    (index : Nat) (point : ∀ b ∈ bounds, b.1 = b.2)
    (finished : Finished (inspectMany state (bases.map .scalar) bounds (fun _ => none) index)) :
    ∃ entries : List (Fin state.base.slots × Inference.Base),
      queries entries = bases.map .scalar ∧ points entries = bounds ∧ Observed state entries := by
  induction bases generalizing bounds index with
  | nil =>
    cases bounds with
    | nil => exact ⟨[],rfl,rfl,by simp [Observed]⟩
    | cons b rest => simp [inspectMany,Finished] at finished
  | cons base bases ih =>
    cases bounds with
    | nil => simp [inspectMany,Finished] at finished
    | cons b rest =>
      have same := point b (by simp)
      cases b with
      | mk low high =>
        change low = high at same
        subst high
        simp only [List.map_cons,inspectMany] at finished
        have parts := (finished_append _ _).mp finished
        have observed := GeneralDictionaryCenteredScalarDiscovery177.scalar_finished state low base none parts.1
        obtain ⟨entries,queriesEq,pointsEq,observedTail⟩ := ih rest (index+1)
          (fun b hb => point b (by simp [hb])) parts.2
        refine ⟨(low,base)::entries,?_,?_,?_⟩
        · exact congrArg (List.cons (.scalar base)) queriesEq
        · exact congrArg (List.cons (low,low)) pointsEq
        · intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact observed
          · exact observedTail entry member

theorem locate_points (state : GeneralSourceState.State)
    (args : List GeneralSourceState.Interval) (bounds)
    (point : ∀ p ∈ args, p.1 = p.2)
    (located : GeneralCandidateBoundaryParts.locate state args = some bounds) :
    ∀ b ∈ bounds, b.1 = b.2 := by
  induction args generalizing bounds with
  | nil => simp [GeneralCandidateBoundaryParts.locate] at located; subst bounds; simp
  | cons a tail ih =>
    have same := point a (by simp)
    cases h : GeneralDictionaryBinderLocations.sourceSlot state a.2 with
    | none => simp [GeneralCandidateBoundaryParts.locate,List.mapM_cons,same,h] at located
    | some slot =>
      simp [GeneralCandidateBoundaryParts.locate,List.mapM_cons,same,h] at located
      change (GeneralCandidateBoundaryParts.locate state tail).bind
        (fun rest => some ((slot,slot) :: rest)) = some bounds at located
      cases ht : GeneralCandidateBoundaryParts.locate state tail with
      | none => simp [ht] at located
      | some rest =>
        simp [ht] at located
        subst bounds
        intro b member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact ih rest (fun p hp => point p (by simp [hp])) ht b member


theorem terminal_branch (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context root declaration) (terminal : declaration.requirements = [])
    (outputs : root.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked (points shape.entries) model := by
  have privateValid := private_models registry context root declaration shape model valid
  refine ⟨privateValid.1,privateValid.2,?_⟩
  rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked terminal outputs]
  exact GeneralNominalMaterialization.empty_models ..

 theorem root_evidence {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (candidate : Candidate registry state root key children plan) (bases : List Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = bases.map .scalar)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model root (.node key []) := by
  obtain ⟨metadata,linked,fresh,bounds,located,finished,ready,consistent⟩ := candidate.prepared
  have pts : ∀ b ∈ bounds, b.1 = b.2 := by
    apply locate_points plan.packet.context.state.base (List.ofFn root.demand.arguments) bounds
    · intro p member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      exact GeneralDictionaryCenteredRootScalar177.root_point reachable index
    · rw [candidate.occurrence_eq] at located
      exact located
  have fi : Finished (inspectMany plan.packet.context.state (bases.map .scalar) bounds (fun _ => none) 0) := by
    simpa only [report,query,Finished] using finished
  obtain ⟨entries,qe,pe,obs⟩ := recover_entries plan.packet.context.state bases bounds 0 pts fi
  let shape : Shape plan.packet.context plan.packet.site.occurrence plan.packet.declaration :=
    ⟨by simpa only [candidate.occurrence_eq] using candidate.role,entries,obs,inputs,
      query.trans qe.symm,by rw [pe]; exact located,by intro out member; rw [outputs] at member; cases member⟩
  have branch := terminal_branch plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration plan.packet.checked shape terminal outputs model
    (by rw [candidate.context_eq]; exact valid.1.1)
  have packetBounds : plan.packet.bounds = bounds := Option.some.inj (candidate.located.symm.trans located)
  have holds : plan.packet.Holds model := by
    change BranchModels _ _ _ _ _ _ _
    rw [packetBounds,← pe]
    exact branch
  have instanceRule := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model holds
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at instanceRule
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model root key).mpr instanceRule

end Yulang.GeneralDictionaryCenteredScalarMany177
