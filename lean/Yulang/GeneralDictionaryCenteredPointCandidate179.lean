import Yulang.GeneralDictionaryCenteredPointJoint179
import Yulang.GeneralDictionaryCenteredRootNominal178

/-! Discover the finite leaf from the real candidate, then construct a common
initial centered model. This theorem does not cover pre-existing plan journals. -/
namespace Yulang.GeneralDictionaryCenteredPointCandidate179
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates GeneralNominalSpineFacts
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryLinearLeaf
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem discovered_shape (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (name : Nat)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = []) :
    Nonempty (LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration) := by
  obtain ⟨_,_,_,points,found,finished,_,_⟩ := candidate.prepared
  have same := Option.some.inj (found.symm.trans located)
  subst points
  have fi : Finished (inspect plan.packet.context.state (.nominal name (List.ofFn fun i => .variables [names i]))
      (slot,slot) none) := by
    simpa only [Finished,report,query,inspectMany,Report.append,List.append_nil] using finished
  obtain ⟨bounds,spine,spineQuery⟩ := GeneralDictionary171InputDiscovery.inspected_leaf
    plan.packet.context.state name names slot none fi
  cases spine with
  | leaf slot descriptor recorded parameters =>
    have sameName := (GeneralNominalInspection.Query.nominal.inj spineQuery).1
    exact ⟨⟨terminal,outputs,by rw [candidate.occurrence_eq]; exact candidate.role,
      slot,descriptor,recorded,n,names,distinct,inputs,bounds,parameters,
      by rw [sameName]; exact query,located⟩⟩
  | wrap slot child descriptor recorded parameters rest =>
    have sameArgs := (GeneralNominalInspection.Query.nominal.inj spineQuery).2
    have member : rest.query ∈ List.ofFn (fun i => GeneralNominalInspection.Query.variables [names i]) := by
      rw [← sameArgs]; exact List.mem_singleton_self _
    obtain ⟨i,equal⟩ := List.mem_ofFn.mp member
    cases rest <;> simp only [Spine.query] at equal <;> cases equal

 theorem initial_joint
    {context : Context} {input : Site roles}
    (candidate : Candidate registry (initialAt context input) focus key children plan)
    (named : input.PointNames)
    (below : ∀ name ∈ GeneralNominalState.sources context.state, name ≤ context.state.seed)
    (slot : Fin plan.packet.context.state.base.slots) (name : Nat)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (previous : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state previous) :
    ∃ extended, Models (initialAt context input) extended ∧ plan.Holds extended ∧
      ∀ name ∈ GeneralNominalState.sources context.state, extended name = previous name := by
  obtain ⟨shape⟩ := discovered_shape candidate slot name names distinct inputs query located terminal outputs
  have packetLocated : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  have inputEq : plan.input = input := List.mem_singleton.mp candidate.centered_recorded
  have contextEq : plan.packet.context = context := candidate.context_eq
  have namedPlan : plan.input.PointNames := by rw [inputEq]; exact named
  obtain ⟨extended,models,holds,kept⟩ := GeneralDictionaryCenteredPointJoint179.joint_model plan shape
    packetLocated namedPlan (by rw [contextEq]; exact below) previous (by rw [contextEq]; exact valid)
  rw [contextEq,inputEq] at models
  rw [contextEq] at kept
  exact ⟨extended,models,holds,kept⟩

end Yulang.GeneralDictionaryCenteredPointCandidate179
