import Yulang.GeneralDictionaryNominalPairDiscovery178
import Yulang.GeneralDictionaryNominalPairShared178

/-! Recover repeated-name nonpoint nominal shapes from actual inspection.
The current-model residual separates semantic sharing from fresh merges. -/
namespace Yulang.GeneralDictionaryNominalSharedDiscovery179
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionaryNominalPairDiscovery178 GeneralDeclarations GeneralSourceDictionaries
 theorem shared_shape_exists (context : Context) (declaration : Declaration)
    (lower upper : Fin context.state.base.slots) (different : lower ≠ upper)
    (name : Nat) (names : Fin n → Nat)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal name (List.ofFn fun i => .variables [names i])])
    (finished : Finished (report context declaration [(lower,upper)])) :
    ∃ shape : GeneralDictionaryNominalPairShared178.SharedShape context declaration,
      shape.lower = lower ∧ shape.upper = upper ∧ shape.left.declaration.name = name ∧ shape.n = n ∧ HEq shape.names names := by
  have fi : Finished (inspect context.state (.nominal name (List.ofFn fun i => .variables [names i]))
      (lower,upper) none) := by
    simpa only [Finished,report,query,inspectMany,Report.append,List.append_nil] using finished
  obtain ⟨left,right,low,high,recorded,recordedRight,leftName,rightName,lowFound,highFound,lowLength,highLength⟩ :=
    nominal_pair context.state name _ lower upper different none fi
  obtain ⟨lows,lowParameters⟩ := vector_parameters left.arguments low lowFound (by simpa using lowLength : n = low.length)
  obtain ⟨highs,highParameters⟩ := vector_parameters right.arguments high highFound (by simpa using highLength : n = high.length)
  refine ⟨⟨lower,upper,different,left,right,recorded,recordedRight,rightName.trans leftName.symm,
    n,names,lows,highs,lowParameters,highParameters,?_⟩,rfl,rfl,leftName,rfl,HEq.rfl⟩
  rw [leftName]
  exact query

open GeneralNominalCenters GeneralNominalCenteredSteps GeneralDictionaryCenteredCandidate176
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

theorem candidate_holds_iff_shared_merges
    (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots) (different : lower ≠ upper)
    (name : Nat) (names : Fin n → Nat)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model ↔
      GeneralNominalSharedCaptureFacts.Coherent model (plan.packet.context.state.base.source lower) name names ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
          plan.packet.site.occurrence.identity plan.packet.declaration
          (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds))) := by
  obtain ⟨_,_,_,bounds,found,finished,_,_⟩ := candidate.prepared
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  obtain ⟨shape,lo,hi,head,arity,parameters⟩ := shared_shape_exists plan.packet.context
    plan.packet.declaration lower upper different name names query finished
  have ordered := GeneralDictionaryCenteredScalarIntervals177.candidate_ordered candidate model valid
    [(lower,upper)] located
  have source : GeneralNominalState.Models plan.packet.context.state model := by
    rw [candidate.context_eq]; exact valid.1.1
  have packetBounds := Option.some.inj (candidate.located.symm.trans located)
  have exactResidual := GeneralDictionaryNominalPairShared178.branch_models_iff_shared_residual
    plan.packet.context plan.packet.registry plan.packet.site.occurrence plan.packet.declaration
    plan.packet.checked shape terminal outputs model
  subst n
  have namesEq := eq_of_heq parameters
  rw [lo,hi,head,namesEq] at exactResidual
  change BranchModels _ _ _ _ _ _ _ ↔ _
  rw [packetBounds,exactResidual]
  exact ⟨fun given => given.2.2,fun given => ⟨source,ordered (lower,upper) (by simp),given⟩⟩

theorem candidate_evidence
    (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots) (different : lower ≠ upper)
    (name : Nat) (names : Fin n → Nat)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (coherent : GeneralNominalSharedCaptureFacts.Coherent model
      (plan.packet.context.state.base.source lower) name names)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration
        (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds)))) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have holds := (candidate_holds_iff_shared_merges candidate lower upper different name names query located
    terminal outputs model valid).mpr ⟨coherent,merges⟩
  have inst := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model holds
  rw [GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal] at inst
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr inst

end Yulang.GeneralDictionaryNominalSharedDiscovery179
