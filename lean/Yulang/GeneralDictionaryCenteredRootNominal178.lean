import Yulang.GeneralDictionaryCenteredNullary178
import Yulang.GeneralDictionaryReachableRootIntervals

/-! Pointness of the original G root localizes every successful singleton
inspection to one slot. Finite linear terminal nominal heads therefore have
same-model root evidence. This makes no assertion about generated children. -/
namespace Yulang.GeneralDictionaryCenteredRootNominal178
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176
open GeneralNominalRecursiveCandidates
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem root_point
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state) :
    ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2 := by
  obtain ⟨start,⟨context,labels,source,point,ground,equal⟩,path⟩ := reachable
  exact point

 theorem located_point (context : Context) (root : Occurrence roles)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (lower upper : Fin context.state.base.slots)
    (located : arguments context root = some [(lower,upper)]) : lower = upper := by
  have recovered := GeneralDictionaryReachableRootIntervals.locate_sources context.state.base
    (List.ofFn root.demand.arguments) [(lower,upper)] located
  have member : (context.state.base.source lower,context.state.base.source upper) ∈ List.ofFn root.demand.arguments := by
    rw [← recovered]
    exact List.mem_singleton_self _
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp member
  apply context.state.base.source_injective
  have result := point index
  rw [equal] at result
  exact result

 theorem reachable_root_point_bounds
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (candidate : Candidate registry state root key children plan)
    (q : GeneralNominalInspection.Query)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [q]) :
    ∃ slot, arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)] := by
  obtain ⟨lower,upper,bounds⟩ := GeneralDictionaryCenteredNullary178.candidate_singleton_bounds candidate q query
  have located := candidate.located
  rw [bounds] at located
  have rootLocated := located
  rw [candidate.occurrence_eq] at rootLocated
  have same := located_point plan.packet.context root (root_point reachable) lower upper rootLocated
  subst upper
  exact ⟨lower,located⟩

/-- A finite linear head format for one role. Associated declarations and
requirements are absent; no model-indexed premise occurs in this format. -/
def LinearTerminalAt (registry : Registry) (context : Context) (role : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.role = role →
    declaration.associated = [] ∧ declaration.requirements = [] ∧
    ∃ (n name : Nat) (names : Fin n → Nat), Function.Injective names ∧
      declaration.inputNames = List.ofFn names ∧
      GeneralNominalInspection.queries context.state context.interpretation declaration =
        [.nominal name (List.ofFn fun i => .variables [names i])]

 theorem point_linear_evidence_at_G_root
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (selected : GeneralNominalCenteredBoundary.Local registry state root (.selected key children))
    (format : LinearTerminalAt registry state.erased.current.context root.demand.role)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model root (.node key dictionaries) := by
  obtain ⟨plan,candidate⟩ := reachable_candidate reachable (.inl rfl) selected
  obtain ⟨outputs,terminal,n,name,names,distinct,inputs,query⟩ := format _ candidate.visible candidate.role
  have queryHere : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])] := by
    rw [candidate.context_eq]
    exact query
  obtain ⟨slot,located⟩ := reachable_root_point_bounds reachable candidate _ queryHere
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at given
  cases given
  exact GeneralDictionaryCenteredNominalPoint178.point_evidence candidate slot name names distinct inputs
    queryHere located terminal (GeneralDictionaryCenteredNullary178.candidate_no_outputs candidate outputs) model valid
end Yulang.GeneralDictionaryCenteredRootNominal178
