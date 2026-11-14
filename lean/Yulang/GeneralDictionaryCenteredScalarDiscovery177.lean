import Yulang.GeneralDictionaryCenteredScalar177

/-! Recover structural scalar witnesses from the successful actual inspection.
The syntactic fragment has one point scalar argument, no binders, outputs or
where requirements. No hypothesis about the observed normalized head is given. -/
namespace Yulang.GeneralDictionaryCenteredScalarDiscovery177
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryCenteredScalar177

 theorem scalar_finished (state : GeneralNominalState.State)
    (slot : Fin state.base.slots) (base : Inference.Base)
    (origin : Option Origin)
    (finished : Finished (inspect state (.scalar base) (slot,slot) origin)) :
    state.nominals slot = none ∧ state.view.heads slot = .scalar base := by
  cases hn : state.nominals slot with
  | some value => simp [inspect,hn,Report.visit,Finished] at finished
  | none =>
    refine ⟨rfl,?_⟩
    cases hh : state.view.heads slot <;>
      simp [inspect,hn,hh,Report.visit,Finished,block] at finished
    rename_i actual
    split at finished
    next h => simp [h]
    next h => simp at finished

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

/-- A selected candidate's own Prepared inspection recovers the scalar state
witness. The remaining premises describe only declaration syntax and the
single point argument lookup. -/
def discover_shape {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (base : Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base])
    (point : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)]) :
    GeneralDictionaryScalarLeaf.ScalarLeafShape plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration := by
  have fi : Finished (inspect plan.packet.context.state (.scalar base) (slot,slot) none) := by
    obtain ⟨metadata,linked,_,bounds,located,finished,_,_⟩ := candidate.prepared
    have same := Option.some.inj (located.symm.trans point)
    subst bounds
    simpa only [report,query,inspectMany,Report.append,List.append_nil,Finished] using finished
  have shape := scalar_finished _ slot base none fi
  exact ⟨terminal,outputs,by simpa only [candidate.occurrence_eq] using candidate.role,
    slot,base,shape.1,shape.2,inputs,query,point⟩

theorem discovered_committed {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (base : Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base])
    (point : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)]) :
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet :=
  scalar_candidate_committed candidate (discover_shape candidate slot base terminal outputs inputs query point)

theorem discovered_instance {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (base : Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base])
    (point : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.erased.current.context model focus key children :=
  committed_candidate_instance candidate
    (discovered_committed candidate slot base terminal outputs inputs query point) model valid

theorem discovered_children_empty {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (terminal : plan.packet.declaration.requirements = []) :
    children = [] := by
  rw [← candidate.children_eq]
  exact GeneralDictionaryLinearLeaf.children_empty plan.packet.context plan.packet.registry
    plan.packet.site.occurrence plan.packet.declaration plan.packet.checked terminal _

theorem discovered_evidence {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (base : Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base])
    (point : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have instanceRule := discovered_instance candidate slot base terminal outputs inputs query point model valid
  have empty := discovered_children_empty candidate terminal
  rw [empty] at instanceRule
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr instanceRule


end Yulang.GeneralDictionaryCenteredScalarDiscovery177
