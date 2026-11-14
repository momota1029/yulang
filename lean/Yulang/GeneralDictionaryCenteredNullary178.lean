import Yulang.GeneralDictionaryCenteredNominalPoint178

/-! Binderless terminal nominal selections give evidence in the unchanged G
boundary. This is a syntactically restricted field-shaped consumer, not a
replacement Checked predicate or the unrestricted EvidenceNode theorem. -/
namespace Yulang.GeneralDictionaryCenteredNullary178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem candidate_singleton_bounds (candidate : Candidate registry state focus key children plan)
    (q : GeneralNominalInspection.Query)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [q]) :
    ∃ lower upper, plan.packet.bounds = [(lower,upper)] := by
  obtain ⟨_,_,_,bounds,found,finished,_,_⟩ := candidate.prepared
  have same := Option.some.inj (candidate.located.symm.trans found)
  have fi : Finished (inspectMany plan.packet.context.state [q] bounds (fun _ => none) 0) := by
    simpa only [Finished,report,query] using finished
  have length := GeneralDictionaryNominalPairDiscovery178.many_length _ _ _ _ _ fi
  have lengthOne : bounds.length = 1 := by simpa using length.symm
  cases bounds with
  | nil => simp at lengthOne
  | cons pair tail =>
    cases tail with
    | nil => exact ⟨pair.1,pair.2,same⟩
    | cons other rest => simp at lengthOne

 theorem candidate_no_outputs (candidate : Candidate registry state focus key children plan)
    (none : plan.packet.declaration.associated = []) : plan.packet.site.occurrence.demand.outputs = [] := by
  obtain ⟨_,_,_,_,_,_,ready,_⟩ := candidate.prepared
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨equation,present,_⟩ := ready.1 output member
  rw [none] at present
  cases present

 theorem candidate_evidence (candidate : Candidate registry state focus key children plan)
    (name : Nat) (inputs : plan.packet.declaration.inputNames = [])
    (outputs : plan.packet.declaration.associated = [])
    (terminal : plan.packet.declaration.requirements = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name []])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  obtain ⟨lower,upper,bounds⟩ := candidate_singleton_bounds candidate _ query
  exact GeneralDictionaryCenteredNominalPoint178.nullary_evidence candidate lower upper name inputs query
    (by rw [← bounds]; exact candidate.located) terminal (candidate_no_outputs candidate outputs) model valid

/-- A role-local syntax restriction; it has no model, Evidence, source-shape,
installation, reachability or stability premise. -/
def NullaryAt (registry : Registry) (context : Context) (role : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.role = role →
    declaration.inputNames = [] ∧ declaration.associated = [] ∧ declaration.requirements = [] ∧
    ∃ name, GeneralNominalInspection.queries context.state context.interpretation declaration = [.nominal name []]

 theorem evidence_at_G {root : Occurrence roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (reached : focus = root ∨ GeneralNominalSaturationState.Generated state.erased.current root focus)
    (selected : GeneralNominalCenteredBoundary.Local registry state focus (.selected key children))
    (format : NullaryAt registry state.erased.current.context focus.demand.role)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key dictionaries) := by
  obtain ⟨plan,candidate⟩ := reachable_candidate reachable reached selected
  obtain ⟨inputs,outputs,terminal,name,query⟩ := format _ candidate.visible candidate.role
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at given
  cases given
  exact candidate_evidence candidate name inputs outputs terminal
    (by rw [candidate.context_eq]; exact query) model valid

end Yulang.GeneralDictionaryCenteredNullary178
