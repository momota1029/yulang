import Yulang.GeneralDictionaryCenteredRootNominal178
import Yulang.GeneralDictionary172CoverageSyntax

/-! Finite linear unary-depth nominal certificates for exact centered candidates.
Actual completed inspection discovers the spine. PointInspection remains an
explicit structural restriction, not a premise about the desired model. -/
namespace Yulang.GeneralDictionaryCenteredNested179
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176
open GeneralDictionary171LocalInspectionObservation (PointInspection)
open GeneralDictionary172CoverageInput (Syntax)
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem nested_holds (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (q : GeneralNominalInspection.Query)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (form : Syntax names q)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [q])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (points : PointInspection plan.packet.context.state (report plan.packet.context plan.packet.declaration [(slot,slot)]))
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) : plan.packet.Holds model := by
  obtain ⟨_,_,_,bs,found,finished,_,_⟩ := candidate.prepared
  have same := Option.some.inj (found.symm.trans located)
  subst bs
  have fi : Finished (inspect plan.packet.context.state q (slot,slot) none) := by
    simpa only [Finished,report,query,inspectMany,Report.append,List.append_nil] using finished
  have pi : PointInspection plan.packet.context.state (inspect plan.packet.context.state q (slot,slot) none) := by
    simpa only [PointInspection,report,query,inspectMany,Report.append,List.append_nil] using points
  obtain ⟨bounds,spine,spineQuery⟩ := GeneralDictionary172CoverageInput.inspected_spine
    plan.packet.context.state names form slot none fi pi
  have translated : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [spine.query] := by rw [spineQuery]; exact query
  have priv := GeneralNominalSpineFacts.private_models plan.packet.context plan.packet.registry
    plan.packet.site.occurrence plan.packet.declaration names distinct inputs bounds spine translated model
    (by rw [candidate.context_eq]; exact valid.1.1)
  have packetBounds := Option.some.inj (candidate.located.symm.trans located)
  change BranchModels _ _ _ _ _ _ _
  rw [packetBounds]
  refine ⟨priv.1,priv.2,?_⟩
  rw [GeneralDictionaryLinearLeaf.generated_empty _ _ _ _ _ terminal outputs]
  exact GeneralNominalMaterialization.empty_models ..

 theorem nested_evidence (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (q : GeneralNominalInspection.Query)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (form : Syntax names q)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [q])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (points : PointInspection plan.packet.context.state (report plan.packet.context plan.packet.declaration [(slot,slot)]))
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have inst := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model
    (nested_holds candidate slot q names distinct inputs form query located points terminal outputs model valid)
  rw [GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal] at inst
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr inst

 theorem recognized_evidence (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (q : GeneralNominalInspection.Query)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (accepted : GeneralDictionary172CoverageSyntax.recognize names q = true)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [q])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (points : PointInspection plan.packet.context.state (report plan.packet.context plan.packet.declaration [(slot,slot)]))
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) :=
  nested_evidence candidate slot q names distinct inputs
    (GeneralDictionary172CoverageSyntax.recognize_sound names q accepted) query located points terminal outputs model valid

 theorem candidate_point_bounds (candidate : Candidate registry state focus key children plan)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (q : GeneralNominalInspection.Query)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [q]) :
    ∃ slot, arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)] := by
  obtain ⟨lower,upper,bounds⟩ := GeneralDictionaryCenteredNullary178.candidate_singleton_bounds candidate q query
  have located := candidate.located
  rw [bounds] at located
  have focusLocated := located
  rw [candidate.occurrence_eq] at focusLocated
  have same := GeneralDictionaryCenteredRootNominal178.located_point plan.packet.context focus point lower upper focusLocated
  subst upper
  exact ⟨lower,located⟩

/-- Syntax and actual-report structural obligations for one role. The bounds
are universal only to make this independent of a selected plan. -/
def NestedTerminalAt (registry : Registry) (context : Context) (role : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.role = role →
    declaration.associated = [] ∧ declaration.requirements = [] ∧
    ∃ (n : Nat) (names : Fin n → Nat) (q : GeneralNominalInspection.Query),
      Function.Injective names ∧ declaration.inputNames = List.ofFn names ∧
      Syntax names q ∧ GeneralNominalInspection.queries context.state context.interpretation declaration = [q] ∧
      ∀ slot, PointInspection context.state (report context declaration [(slot,slot)])

 theorem nested_evidence_at_G {root : Occurrence roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (reached : focus = root ∨ GeneralNominalSaturationState.Generated state.erased.current root focus)
    (selected : GeneralNominalCenteredBoundary.Local registry state focus (.selected key children))
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (format : NestedTerminalAt registry state.erased.current.context focus.demand.role)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key dictionaries) := by
  obtain ⟨plan,candidate⟩ := reachable_candidate reachable reached selected
  obtain ⟨outputs,terminal,n,names,q,distinct,inputs,form,query,points⟩ := format _ candidate.visible candidate.role
  have queryHere : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [q] := by rw [candidate.context_eq]; exact query
  obtain ⟨slot,located⟩ := candidate_point_bounds candidate point q queryHere
  have pointsHere : PointInspection plan.packet.context.state
      (report plan.packet.context plan.packet.declaration [(slot,slot)]) := by
    revert slot
    rw [candidate.context_eq]
    intro slot _
    exact points slot
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at given
  cases given
  exact nested_evidence candidate slot q names distinct inputs form queryHere located pointsHere terminal
    (GeneralDictionaryCenteredNullary178.candidate_no_outputs candidate outputs) model valid

 theorem nested_evidence_at_G_root {root : Occurrence roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (selected : GeneralNominalCenteredBoundary.Local registry state root (.selected key children))
    (format : NestedTerminalAt registry state.erased.current.context root.demand.role)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model root (.node key dictionaries) :=
  nested_evidence_at_G reachable (.inl rfl) selected
    (GeneralDictionaryCenteredRootNominal178.root_point reachable) format model valid dictionaries given
end Yulang.GeneralDictionaryCenteredNested179
