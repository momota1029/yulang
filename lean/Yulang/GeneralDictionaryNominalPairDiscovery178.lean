import Yulang.GeneralDictionary171InputDiscovery
import Yulang.GeneralDictionaryCenteredNominal178
import Yulang.GeneralNominalInspectionAlignment

/-! Recover nonpoint nominal-pair descriptors and both parameter vectors from
successful actual inspection. Shape witnesses are produced, not assumed. -/
namespace Yulang.GeneralDictionaryNominalPairDiscovery178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalInspection (Query)
open GeneralNominalInspectionAlignment
open GeneralDeclarations GeneralSourceDictionaries

 theorem many_length (state : GeneralNominalState.State)
    (queries : List Query) (bounds : List (GeneralNominalInspection.Bounds state))
    (origins : Nat → Option Origin) (index : Nat)
    (finished : Finished (inspectMany state queries bounds origins index)) : queries.length = bounds.length := by
  induction queries generalizing bounds index with
  | nil => cases bounds with
    | nil => rfl
    | cons b bs => simp [inspectMany,Finished] at finished
  | cons q qs ih => cases bounds with
    | nil => simp [inspectMany,Finished] at finished
    | cons b bs =>
      rw [inspectMany] at finished
      simpa using ih bs (index+1) ((finished_append _ _).mp finished).2

 theorem nominal_pair (state : GeneralNominalState.State) (name : Nat)
    (queries : List Query) (lower upper : Fin state.base.slots) (different : lower ≠ upper)
    (origin : Option Origin)
    (finished : Finished (inspect state (.nominal name queries) (lower,upper) origin)) :
    ∃ left right low high,
      state.nominals lower = some left ∧ state.nominals upper = some right ∧
      left.declaration.name = name ∧ right.declaration.name = name ∧
      typeArguments left.arguments = some low ∧ typeArguments right.arguments = some high ∧
      queries.length = low.length ∧ queries.length = high.length := by
  simp only [inspect,finished_visit] at finished
  split at finished
  · split at finished <;> simp [Finished,block] at finished
  · rename_i descriptor recorded
    split at finished
    · rename_i same
      split at finished
      · simp [Finished,block] at finished
      · rename_i intervals found
        split at finished
        · simp [Finished,block] at finished
        · rename_i upperDescriptor upperAt
          split at finished
          · rename_i upperName
            split at finished
            · simp [Finished,block] at finished
            · rename_i targets upperArgs
              have both := (finished_append ..).mp finished
              exact ⟨descriptor,upperDescriptor,intervals,targets,recorded,upperAt,same,upperName,
                found,upperArgs,many_length _ _ _ _ _ both.1,many_length _ _ _ _ _ both.2⟩
          · simp [Finished] at finished
    · simp [Finished] at finished

 theorem vector_parameters (parameters : List (GeneralNominalState.Parameter slots))
    (intervals : List (Fin slots × Fin slots)) (found : typeArguments parameters = some intervals)
    (length : n = intervals.length) :
    ∃ bounds : Fin n → Fin slots × Fin slots,
      parameters = List.ofFn fun i => GeneralNominalState.Parameter.type (bounds i) := by
  let bounds : Fin n → Fin slots × Fin slots := fun i => intervals[i.val]'(by omega)
  have equation : List.ofFn bounds = intervals := by
    apply List.ext_getElem
    · simp [length]
    · intro i hi hj; simp [bounds]
  refine ⟨bounds,?_⟩
  rw [GeneralDictionary171InputDiscovery.type_arguments_exact parameters intervals found,← equation,List.map_ofFn]
  rfl

 theorem shape_exists (context : Context) (declaration : Declaration)
    (lower upper : Fin context.state.base.slots) (different : lower ≠ upper)
    (name : Nat) (names : Fin n → Nat) (distinct : Function.Injective names)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal name (List.ofFn fun i => .variables [names i])])
    (finished : Finished (report context declaration [(lower,upper)])) :
    ∃ shape : GeneralDictionaryNominalPair178.Shape context declaration,
      shape.lower = lower ∧ shape.upper = upper := by
  have fi : Finished (inspect context.state (.nominal name (List.ofFn fun i => .variables [names i]))
      (lower,upper) none) := by
    simpa only [Finished,report,query,inspectMany,Report.append,List.append_nil] using finished
  obtain ⟨left,right,low,high,recorded,recordedRight,leftName,rightName,lowFound,highFound,lowLength,highLength⟩ :=
    nominal_pair context.state name _ lower upper different none fi
  obtain ⟨lows,lowParameters⟩ := vector_parameters left.arguments low lowFound (by simpa using lowLength : n = low.length)
  obtain ⟨highs,highParameters⟩ := vector_parameters right.arguments high highFound (by simpa using highLength : n = high.length)
  refine ⟨⟨lower,upper,different,left,right,recorded,recordedRight,rightName.trans leftName.symm,
    n,names,distinct,lows,highs,lowParameters,highParameters,?_⟩,rfl,rfl⟩
  rw [leftName]
  exact query

open GeneralNominalCenters GeneralNominalCenteredSteps GeneralDictionaryCenteredCandidate176
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem candidate_shape_exists (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots) (different : lower ≠ upper)
    (name : Nat) (names : Fin n → Nat) (distinct : Function.Injective names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)]) :
    ∃ shape : GeneralDictionaryNominalPair178.Shape plan.packet.context plan.packet.declaration,
      arguments plan.packet.context plan.packet.site.occurrence = some [(shape.lower,shape.upper)] := by
  obtain ⟨_,_,_,bounds,found,finished,_,_⟩ := candidate.prepared
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  obtain ⟨shape,lo,hi⟩ := shape_exists plan.packet.context plan.packet.declaration
    lower upper different name names distinct query finished
  exact ⟨shape,by rw [lo,hi]; exact located⟩

/-- Only the query format and its located nonpoint bounds remain as structural
premises. Both descriptors and every parameter interval are discovered. -/
 theorem candidate_holds_iff_merges (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots) (different : lower ≠ upper)
    (name : Nat) (names : Fin n → Nat) (distinct : Function.Injective names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model ↔ PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration
        (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds))) := by
  obtain ⟨shape,found⟩ := candidate_shape_exists candidate lower upper different name names distinct query located
  exact GeneralDictionaryCenteredNominal178.candidate_holds_iff_merges candidate shape found terminal outputs model valid

 theorem candidate_evidence (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots) (different : lower ≠ upper)
    (name : Nat) (names : Fin n → Nat) (distinct : Function.Injective names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration
        (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds)))) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model focus (.node key []) := by
  have holds := (candidate_holds_iff_merges candidate lower upper different name names distinct query located terminal outputs model valid).mpr merges
  have inst := GeneralDictionaryCenteredScalar177.candidate_instance_of_holds candidate model holds
  have empty := GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate terminal
  rw [empty] at inst
  exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry
    state.erased.current.context model focus key).mpr inst

end Yulang.GeneralDictionaryNominalPairDiscovery178
