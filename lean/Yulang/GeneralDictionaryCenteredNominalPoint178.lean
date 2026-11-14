import Yulang.GeneralDictionaryNominalPairDiscovery178

/-! Unconditional same-model producers for point outer nominal arguments with
linear type binders, and for nullary nominal heads at arbitrary endpoint slots.
These are fragments, not the unrestricted ground-boundary EvidenceNode field. -/
namespace Yulang.GeneralDictionaryCenteredNominalPoint178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem point_holds (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (name : Nat)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) : plan.packet.Holds model := by
  obtain ⟨_,_,_,points,found,finished,_,_⟩ := candidate.prepared
  have same := Option.some.inj (found.symm.trans located)
  subst points
  have fi : Finished (inspect plan.packet.context.state (.nominal name (List.ofFn fun i => .variables [names i]))
      (slot,slot) none) := by
    simpa only [Finished,report,query,inspectMany,Report.append,List.append_nil] using finished
  obtain ⟨bounds,spine,spineQuery⟩ := GeneralDictionary171InputDiscovery.inspected_leaf
    plan.packet.context.state name names slot none fi
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

 theorem point_evidence (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots) (name : Nat)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have inst := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model
    (point_holds candidate slot name names distinct inputs query located terminal outputs model valid)
  rw [GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal] at inst
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr inst

 theorem nullary_holds (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots) (name : Nat)
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name []])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) : plan.packet.Holds model := by
  by_cases same : lower = upper
  · subst upper
    exact point_holds candidate lower name (Fin.elim0 : Fin 0 → Nat) (fun i => Fin.elim0 i)
      (by simpa using inputs) (by simpa using query) located terminal outputs model valid
  · apply (GeneralDictionaryNominalPairDiscovery178.candidate_holds_iff_merges candidate lower upper same name
      (Fin.elim0 : Fin 0 → Nat) (fun i => Fin.elim0 i) (by simpa using query)
      located terminal outputs model valid).mpr
    simp [GeneralNominalAllocation.merges,inputs,PresenceNormalForm.All]

 theorem nullary_evidence (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots) (name : Nat)
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name []])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have inst := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model
    (nullary_holds candidate lower upper name inputs query located terminal outputs model valid)
  rw [GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal] at inst
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr inst

end Yulang.GeneralDictionaryCenteredNominalPoint178
