import Yulang.GeneralNominalCenteredSteps
import Yulang.GeneralNominalGroundExamples
import Yulang.GeneralNominalBranchingMass
import Yulang.GeneralNominalCenteredInitialInventories
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
/-! A checked source with an unknown child and an actual guarded centered installation.
The finite witness establishes every installation guard without a transition premise. -/
namespace Yulang.GeneralNominalCenteredSourceRefreshWitness
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms equationAtoms_exact)

abbrev roles : Roles.RoleDecls := fun role =>
  if role = 0 ∨ role = 1 then GeneralNominalProvenanceDeclarations.outputRole 1 0
  else GeneralNominalProvenanceDeclarations.bareRole 1
abbrev constructors := GeneralDeclarationExamples.constructors
abbrev childR : Clause := ⟨10,1,[.var 0],[⟨100,0,.var 2⟩]⟩
abbrev childS : Clause := ⟨20,2,[.var 0],[]⟩
abbrev p : Declaration := ⟨0,0,[.app 5 [.var 0,.var 1]],[childR],[⟨101,0,.var 2⟩],[⟨2,10,100⟩]⟩
abbrev r : Declaration := ⟨1,1,[.app 5 [.var 0,.var 1]],[childS],[⟨201,0,.var 0⟩],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[p,r]⟩

theorem p_checked : DeclarationChecked constructors roles p := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,
      GeneralNominalProvenanceDeclarations.outputRole,GeneralNominalProvenanceDeclarations.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member
    unfold ConservativeSmaller; decide +kernel
  · intro clause member capture; cases List.mem_singleton.mp member
    constructor
    · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size] <;> omega
    · intro name
      simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]

theorem r_checked : DeclarationChecked constructors roles r := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,
      GeneralNominalProvenanceDeclarations.outputRole,GeneralNominalProvenanceDeclarations.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member
    unfold ConservativeSmaller; decide +kernel
  · intro clause member capture; cases List.mem_singleton.mp member
    constructor
    · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size] <;> omega
    · intro name
      simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  rcases List.mem_cons.mp member with rfl | member
  · exact p_checked
  · cases List.mem_singleton.mp member; exact r_checked

abbrev atoms : List (PresenceNormalForm.Atom (Fin 4)) :=
  equationAtoms 0 (.pair (.var 1) (.var 2)) ++ equationAtoms 1 (.pair (.var 2) (.var 2)) ++ equationAtoms 3 (.base .int)
abbrev rawShapes : Fin 1 → GeneralSourceState.Shape 4 := fun _ => .pair
abbrev rawHeads : Fin 4 → GeneralSourceState.Head rawShapes := fun slot =>
  if slot = 0 then .structural 0 (fun i => if i.val = 0 then 1 else 2) else
  if slot = 1 then .structural 0 (fun _ => 2) else .unresolved
abbrev base : GeneralSourceState.State where
  slots := 4
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := atoms
  kinds := 1
  shapes := rawShapes
  shapes_injective := by intro a b _; exact Subsingleton.elim a b
  heads := rawHeads
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    have facts : PresenceNormalForm.All Common.model assignment (equationAtoms 0 (.pair (.var 1) (.var 2))) ∧
        PresenceNormalForm.All Common.model assignment (equationAtoms 1 (.pair (.var 2) (.var 2))) ∧
        PresenceNormalForm.All Common.model assignment (equationAtoms 3 (.base .int)) := by
      simpa only [atoms,PresenceNormalForm.all_append,and_assoc] using valid
    by_cases zero : slot = 0
    · subst slot
      have equal : (.pair (.var 1) (.var 2) : TyTerm (Fin 4)) = term := by
        simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
      subst term
      exact (equationAtoms_exact ..).mp facts.1
    · by_cases one : slot = 1
      · subst slot
        have equal : (.pair (.var 2) (.var 2) : TyTerm (Fin 4)) = term := by
          simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
        subst term
        exact (equationAtoms_exact ..).mp facts.2.1
      · simp [rawHeads,zero,one,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by intro _ _ _ member; cases member
abbrev shapes : Fin 1 → GeneralNormalizedObservation.Shape := fun _ => .pair
abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 1
  shapes := shapes
  shapes_injective := by intro a b _; exact Subsingleton.elim a b
  canonical := by intro kind; trivial
  heads := fun slot => if slot = 0 then .structural 0 (fun i => if i.val = 0 then 1 else 2) else
    if slot = 1 then .structural 0 (fun _ => 2) else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have equal : (.pair (.var 1) (.var 2) : TyTerm (Fin 4)) = term := by
        simpa [GeneralNormalizedObservation.Head.term,shapes,GeneralNormalizedObservation.Shape.term] using recorded
      subst term
      exact .head rfl
    · by_cases one : slot = 1
      · subst slot
        have equal : (.pair (.var 2) (.var 2) : TyTerm (Fin 4)) = term := by
          simpa [zero,GeneralNormalizedObservation.Head.term,shapes,GeneralNormalizedObservation.Shape.term] using recorded
        subst term
        exact .head rfl
      · simp [zero,one,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded
abbrev source : GeneralNominalState.State := GeneralNominalState.embed base view constructors
abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun key => if key = 5 then some .pair else if key = 2 then some (.scalar .int) else none
  invariantNominal := fun _ => false
  disjoint := by intro _ impossible; cases impossible
abbrev context : GeneralNominalCandidates.Context := ⟨source,interpretation⟩
abbrev root : Occurrence roles := ⟨4,⟨0,fun _ => (0,0),[⟨0,2⟩],by
  intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,⟨rfl,?_⟩,?_,(by intro _ _ _; exact CommonNominalFullCarrier.subtype_refl _),?_,rfl⟩
  · intro key primitive found
    by_cases five : key = 5
    · subst key; cases Option.some.inj found; exact ⟨⟨[.type,.type],5⟩,rfl,rfl⟩
    · by_cases two : key = 2
      · subst key; cases Option.some.inj found; exact ⟨⟨[],2⟩,rfl,rfl⟩
      · simp [interpretation,five,two] at found
  · constructor
    · intro index
      constructor <;> exact GeneralNominalAllocationSupport.slot_source source 0
    · intro output member; cases List.mem_singleton.mp member
      exact GeneralNominalAllocationSupport.slot_source source 2
  · intro identity member
    change identity ≤ 3
    simp [GeneralNominalState.sources,source,GeneralNominalState.embed,List.ofFn_succ] at member
    omega

theorem point : GeneralNominalActualBudget.PointSource context root := by
  refine ⟨?_,?_,?_,fun _ => rfl⟩
  · intro pair member; cases member
  · intro slot descriptor recorded; cases recorded
  · intro slot descriptor recorded; cases recorded

open GeneralNominalSaturationState (Packet)
open GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection
open GeneralNominalPacketSupport
open CommonNominalFullCarrier
abbrev packetP : Packet roles := ⟨registry,context,GeneralNominalDemandMerging.pointSite root,p,p_checked,[(0,0)]⟩
abbrev planP : Plan roles := ⟨packetP,rootSite source.seed root,rfl⟩
abbrev initialState := GeneralNominalCenteredSteps.initial context root
noncomputable abbrev afterP := GeneralNominalCenteredSteps.install initialState planP []
abbrev outputP := GeneralNominalAllocation.source source registry root.identity (GeneralNominalAllocation.origin root.identity p.id 2 2 0)

abbrev reportP : Report source where
  captures := [⟨0,(1,1),none⟩,⟨1,(2,2),none⟩]
  inspected := [(0,0)]
  checked := [(0,0),(0,0),(1,1),(2,2)]
theorem queriesP : GeneralNominalInspection.queries source interpretation p =
    [.node .pair [.variables [0],.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,p,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]
theorem reportP_exact : GeneralNominalPacketSupport.report packetP = reportP := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  have atZero : source.view.heads 0 = .structural 0 (fun i => if i.val = 0 then 1 else 2) := rfl
  change { inspectMany source (GeneralNominalInspection.queries source interpretation p) [(0,0)]
    (fun _ => none) 0 with checked := [(0,0)] ++
    (inspectMany source (GeneralNominalInspection.queries source interpretation p) [(0,0)] (fun _ => none) 0).checked } = _
  rw [queriesP]
  simp only [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_4,atZero]
  change { (Report.visit (0,0) none (.structural .pair)
    (inspectMany source [.variables [0],.variables [1]] [(1,1),(2,2)] (fun _ => none) 0)).append {} with
    checked := [(0,0)] ++ ((Report.visit (0,0) none (.structural .pair)
    (inspectMany source [.variables [0],.variables [1]] [(1,1),(2,2)] (fun _ => none) 0)).append {}).checked } = _
  simp [inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,Report.append,Report.visit,reportP]
theorem bindingsP : packetP.bindings = [(0,(1,1)),(1,(2,2))] := by
  change bindings source (GeneralNominalPacketSupport.report packetP) = _
  rw [reportP_exact]; rfl
theorem p_sorted : GeneralCanonicalChildOrder.canonicalDeclaration p = p := by
  change { p with requirements := GeneralCanonicalChildOrder.canonicalRequirements [childR] } = p
  rw [GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
abbrev schemaP : GeneralNominalMaterialization.Schema where
  variables := [⟨2,.source 2,.actual⟩,⟨2,.source outputP,.actual⟩]
theorem schemaP_exact : namedSchema packetP = schemaP := by
  unfold namedSchema GeneralNominalRecursiveCandidates.generated
  change GeneralNominalMaterialization.generated source interpretation
    (GeneralNominalMaterialization.requests source registry root p p_checked packetP.bindings) = _
  rw [bindingsP]
  unfold GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,p_sorted]
  simp [GeneralNominalMaterialization.requests,GeneralCanonicalChildOrder.canonicalEmit,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton,
    GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,p,root,childR,List.ofFn_succ,List.mergeSort_singleton,
    normalize,normalizeArgs,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
    GeneralDeclarationDemands.outputTarget,GeneralDeclarationDemands.inputInterval,
    GeneralDeclarationDemands.childDemand,Declaration.outputNames,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.allocation,GeneralNominalAllocation.occurrences,schemaP,outputP]
theorem inputSchemaP_exact : inputSchema packetP = {} := by
  unfold inputSchema inputRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,p_sorted]
  simp [packetP,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,p,childR,
    List.ofFn_succ,GeneralNominalMaterialization.inputRequests,
    GeneralDeclarationDemands.childDemand,roles,GeneralNominalProvenanceDeclarations.outputRole,
    normalize,GeneralNominalMaterialization.generated]

def witnessTree (source : Nat) : GeneralNominalBranchingReadback.Tree :=
  if source = 0 then .pair (.pair (.scalar .int) (.scalar .int)) (.scalar .int)
  else if source = 1 then .pair (.scalar .int) (.scalar .int) else .scalar .int
def witness : GeneralNominalCommonBridge.Assignment := fun source => ((witnessTree source).value, Common.rowEmpty)

theorem witness_source : GeneralNominalState.Models source witness := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro atom member
    simp only [base,atoms,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ((rfl|rfl)|(rfl|rfl))|(rfl|rfl)
    all_goals exact subtype_refl _
  · intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have eq : (.pair (.var 1) (.var 2) : TyTerm (Fin 4)) = term := by
        simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
      subst term; exact ⟨subtype_refl _,subtype_refl _⟩
    · by_cases one : slot = 1
      · subst slot
        have eq : (.pair (.var 2) (.var 2) : TyTerm (Fin 4)) = term := by
          simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
        subst term; exact ⟨subtype_refl _,subtype_refl _⟩
      · simp [base,rawHeads,zero,one,GeneralSourceState.Head.equation] at recorded
  · intro bounds member; cases member
  · intro slot desc recorded; cases recorded
  · intro atom member; cases member

theorem projectionP (model : GeneralNominalCommonBridge.Assignment) : ProjectionModels source reportP model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member; cases member
  · intro test member; cases member
  · intro first one last two same ref recorded actual seen
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at one
    rcases one with rfl|rfl <;> cases recorded
  · intro first present last two same a b one two x y hx hy
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl <;> cases one

theorem ordinaryP (model : GeneralNominalCommonBridge.Assignment) : Ordinary packetP model := by
  refine ⟨?_,?_,?_⟩
  · intro first one last two same
    rw [bindingsP] at one two
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl|rfl <;> rcases two with rfl|rfl
    all_goals first | exact subtype_refl _ | cases same
  · have empty : GeneralNominalAllocation.merges source registry root.identity p packetP.bindings = [] := by
      rw [bindingsP]; rfl
    change PresenceNormalForm.All _ _ (GeneralNominalAllocation.merges source registry root.identity p packetP.bindings)
    rw [empty]; exact PresenceNormalForm.all_nil _ _
  · change PresenceNormalForm.All _ _ (selfChecks source (GeneralNominalPacketSupport.report packetP))
    rw [reportP_exact]
    intro atom member
    simp only [selfChecks,reportP,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact subtype_refl _

theorem inputsP (model : GeneralNominalCommonBridge.Assignment) : Inputs packetP model := by
  refine ⟨ordinaryP model,?_,?_⟩
  · change ProjectionModels source (GeneralNominalPacketSupport.report packetP) model
    rw [reportP_exact]; exact projectionP model
  · rw [inputSchemaP_exact]
    exact GeneralNominalMaterialization.empty_models ..

theorem outputP_large : 3 < outputP := GeneralNominalIdentities.source_above_seed source.seed _
theorem witness_output : (witness outputP).1 = .base .int := by
  have zero : outputP ≠ 0 := by have h := outputP_large; omega
  have one : outputP ≠ 1 := by have h := outputP_large; omega
  simp only [witness,witnessTree,ite_eq_right zero,ite_eq_right one]
  rfl

theorem outputsP (model : GeneralNominalCommonBridge.Assignment)
    (out : Equivalent (model 2).1 (model outputP).1) : Outputs packetP model := by
  unfold Outputs
  rw [schemaP_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member; cases member
  · intro entry member
    simp only [schemaP,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      change Equivalent (model 2).1 (model outputP).1
      exact out
    · refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      change Equivalent (model outputP).1 (model outputP).1
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two same firstActual lastActual a b ha hb
    simp only [schemaP,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl|rfl <;> rcases two with rfl|rfl
    all_goals cases ha; cases hb
    · exact ⟨subtype_refl _,subtype_refl _⟩
    · exact out
    · exact ⟨out.2,out.1⟩
    · exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member captured present same actual origin recorded a b ha hb
    change captured ∈ (GeneralNominalPacketSupport.report packetP).captures at present
    rw [reportP_exact] at present
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl <;> cases recorded

theorem packetP_holds : packetP.Holds witness := by
  apply (packet_exact packetP witness).mpr
  refine ⟨witness_source,inputsP witness,outputsP witness ?_⟩
  rw [witness_output]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem locatedP : arguments context root = some [(0,0)] := by decide +kernel

theorem preparedP : Prepared registry context root p p_checked := by
  refine ⟨initial_source.metadata,initial_source.linked,
    GeneralNominalSourceFormation.initial_fresh context initial_source root.identity,
    [(0,0)],locatedP,?_,?_,witness,packetP_holds⟩
  · change Finished (GeneralNominalPacketSupport.report packetP)
    rw [reportP_exact]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro out member; cases List.mem_singleton.mp member
      exact ⟨⟨101,0,.var 2⟩,List.mem_singleton_self _,rfl⟩
    · change (namedSchema packetP).unknown = false
      rw [schemaP_exact]

abbrev height (identity : Nat) := (witnessTree identity).mass

theorem witness_no_nominal (identity name index : Nat) (actual : Ty) :
    ¬ GeneralNominalProjections.Observes witness (.argument (.source identity) name index) (.inl actual) := by
  intro seen
  cases seen with
  | argument parent equal found =>
    cases parent
    change Equivalent (witnessTree identity).value _ at equal
    by_cases zero : identity = 0
    · subst identity
      exact GeneralNominalBranchingReadback.pair_not_nominal _ _ _ _ equal.1
    · by_cases one : identity = 1
      · subst identity
        exact GeneralNominalBranchingReadback.pair_not_nominal _ _ _ _ equal.1
      · have scalar : (witnessTree identity).value = .base .int := by
          simp only [witnessTree,ite_eq_right zero,ite_eq_right one]; rfl
        rw [scalar] at equal
        exact GeneralNominalPeelingOrigins.base_not_nominal _ _ _ equal.1

theorem feedback_acyclic (state : GeneralNominalSaturationState.State roles)
    (valid : GeneralNominalSaturationState.Models state witness)
    (smaller : ∀ first last, GeneralSourceK2.Child state.context.state.view first last →
      height (state.context.state.base.source last) < height (state.context.state.base.source first))
    (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle state identity := by
  have decreases : ∀ first last, GeneralNominalFeedbackK2.Edge state first last → height last < height first := by
    intro first last edge
    rcases edge.2.2 with ⟨parent,child,childEdge,parentEqual,childEqual⟩ | argument
    · have one := GeneralNominalBranchingMass.equivalent_mass (witnessTree first)
        (witnessTree (state.context.state.base.source parent)) (parentEqual witness valid)
      have two := GeneralNominalBranchingMass.equivalent_mass
        (witnessTree (state.context.state.base.source child)) (witnessTree last) (childEqual witness valid)
      have bound := smaller parent child childEdge
      change height first = height (state.context.state.base.source parent) at one
      change height (state.context.state.base.source child) = height last at two
      omega
    · obtain ⟨name,index,actual,seen,_⟩ := GeneralNominalFeedbackK2.argument_sound argument witness valid
      exact False.elim (witness_no_nominal first name index actual seen)
  have paths : ∀ first last, GeneralNominalFeedbackK2.Path state first last → height last ≤ height first := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreases _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := decreases _ _ edge
  have two := paths _ _ path
  omega

theorem raw_acyclic (snapshot : GeneralNominalState.State)
    (none : ∀ slot, snapshot.nominals slot = none)
    (smaller : ∀ first last, GeneralSourceK2.Child snapshot.view first last →
      height (snapshot.base.source last) < height (snapshot.base.source first))
    (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.Cycle snapshot slot := by
  have decreases : ∀ first last, GeneralNominalMixedRecurrence.Edge snapshot first last →
      height (snapshot.base.source last) < height (snapshot.base.source first) := by
    intro first last edge
    rcases edge with structural | ⟨descriptor,recorded,_⟩
    · exact smaller first last structural
    · rw [none first] at recorded; cases recorded
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path snapshot first last →
      height (snapshot.base.source last) ≤ height (snapshot.base.source first) := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreases _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := decreases _ _ edge
  have two := paths _ _ path
  omega

theorem no_legacy (snapshot : GeneralNominalState.State)
    (none : ∀ slot, snapshot.nominals slot = none)
    (smaller : ∀ first last, GeneralSourceK2.Child snapshot.view first last →
      height (snapshot.base.source last) < height (snapshot.base.source first))
    (slot : Fin snapshot.base.slots) : ¬ GeneralNominalMixedRecurrence.RecursAt snapshot slot := by
  have absent := raw_acyclic snapshot none smaller
  have structural : ∀ slot, ¬ GeneralSourceK2.Cycle snapshot.view slot := by
    rintro slot ⟨child,edge,path⟩
    exact absent slot ⟨child,Or.inl edge,GeneralNominalMixedRecurrence.source_path snapshot child slot path⟩
  rintro ⟨_,⟨cycle,_⟩|graph⟩
  · exact absent slot cycle
  · rcases GeneralSourceK2.graphK2_sound snapshot.view slot graph with cycle|⟨_,_,_,other,cycle,_⟩
    · exact structural slot cycle
    · exact structural other cycle

theorem source_smaller (first last : Fin source.base.slots)
    (edge : GeneralSourceK2.Child source.view first last) : height last.val < height first.val := by
  obtain ⟨kind,children,recorded,index,rfl⟩ := edge
  by_cases zero : first = 0
  · subst first
    change GeneralNormalizedObservation.Head.structural 0 (fun i => if i.val = 0 then 1 else 2) = _ at recorded
    cases recorded
    by_cases atZero : index.val = 0
    · simp [height,witnessTree,atZero,GeneralNominalBranchingReadback.Tree.mass]
    · simp [height,witnessTree,atZero,GeneralNominalBranchingReadback.Tree.mass]
  · by_cases one : first = 1
    · subst first
      change GeneralNormalizedObservation.Head.structural 0 (fun _ => 2) = _ at recorded
      cases recorded
      change 1 < 3
      decide +kernel
    · have absent : source.view.heads first = .deferred .unresolved := by
        change (if first = 0 then _ else if first = 1 then _ else _) = _
        rw [ite_eq_right zero,ite_eq_right one]
      rw [absent] at recorded; cases recorded

theorem source_no_raw (slot : Fin source.base.slots) : ¬ GeneralNominalCycleK2.Cycle source slot :=
  raw_acyclic source (fun _ => rfl) source_smaller slot

theorem initial_no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle initialState.erased.current identity :=
  feedback_acyclic initialState.erased.current
    ((GeneralNominalSaturationState.initial_models ..).mpr witness_source) source_smaller identity

theorem no_rootP : ¬ GeneralNominalFeedbackK2.RootK2 initialState.erased.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact source_no_raw slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact initial_no_feedback _ cycle

theorem no_candidateP : ¬ GeneralNominalFeedbackK2.CandidateK2 registry initialState.erased.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact source_no_raw visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact initial_no_feedback _ cycle

theorem rootP_ready : ¬ GeneralNominalState.RootPending source root.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  refine ⟨0,rfl,Or.inl ?_⟩
  intro impossible
  cases impossible

theorem p_only (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (role : declaration.role = root.demand.role) : declaration = p := by
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl|rfl
  · rfl
  · cases role

theorem survivorP : Survivor registry context root p.id packetP.children :=
  ⟨rootP_ready,p,by simp [registry],p_checked,rfl,rfl,[(0,0)],locatedP,preparedP,rfl⟩

theorem selectedP : GeneralNominalFeedbackK2.Local registry initialState.erased.current root
    (.selected p.id packetP.children) := by
  refine .selected ⟨rootP_ready,no_rootP,no_candidateP,?_⟩ ⟨survivorP,?_⟩
  · rintro (pending|⟨_,legacy⟩)
    · obtain ⟨_,declaration,visible,certified,role,_,missing⟩ := pending
      have same := p_only declaration visible role
      subst declaration
      exact missing preparedP
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩|⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · exact no_legacy source (fun _ => rfl) source_smaller slot cycle
      · exact no_legacy source (fun _ => rfl) source_smaller visited.1 cycle
  · intro key kids found
    have copied := found
    obtain ⟨_,declaration,visible,certified,identity,role,_⟩ := found
    have same := p_only declaration visible role
    subst declaration; subst key
    exact ⟨rfl,survivor_children_functional registry checked context root p.id kids packetP.children copied survivorP⟩

theorem enabledP : GeneralNominalFeedbackSteps.Installable registry initialState.erased.current packetP := by
  refine ⟨⟨rfl,rfl,List.mem_singleton_self _,by simp [registry],rfl,locatedP,preparedP,
    GeneralNominalFeedbackK2.selected_legacy selectedP,?_,?_,?_,?_⟩,selectedP,?_⟩
  · intro prior member; cases member
  · intro other member same; cases List.mem_singleton.mp member; exact .refl _
  · exact ⟨witness,(GeneralNominalSaturationState.initial_models ..).mpr witness_source,packetP_holds⟩
  · exact GeneralNominalJointCandidates.initial_joint registry context root p (by simp [registry]) p_checked rfl
      [(0,0)] locatedP preparedP witness packetP_holds
  · intro other member same; cases List.mem_singleton.mp member; exact .refl _

abbrev headSchemaP : GeneralNominalMaterialization.Schema where
  variables := [⟨0,.structural (.source 0) .pair 0,.actual⟩,⟨1,.structural (.source 0) .pair 1,.actual⟩]
  tests := [(.source 0,.structural .pair)]

theorem headSchemaP_exact : planP.headSchema = headSchemaP := by
  unfold Plan.headSchema
  change GeneralNominalMaterialization.schemas
    (GeneralNominalInspection.queries source interpretation p) _ .actual 0 = _
  rw [queriesP]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,planP,packetP,rootSite,root,roles,
    GeneralNominalProvenanceDeclarations.outputRole,List.ofFn_succ,headSchemaP]

theorem binderP_zero : planP.binder 0 = 1 := by
  have cap : (capture packetP).inputs 0 = (1,1) := by unfold capture; rw [bindingsP]; rfl
  simp only [Plan.binder,show (0 : Nat) ∉ packetP.declaration.outputNames by decide +kernel,ite_false,cap]
  rfl
theorem binderP_one : planP.binder 1 = 2 := by
  have cap : (capture packetP).inputs 1 = (2,2) := by unfold capture; rw [bindingsP]; rfl
  simp only [Plan.binder,show (1 : Nat) ∉ packetP.declaration.outputNames by decide +kernel,ite_false,cap]
  rfl
theorem binderP_two : planP.binder 2 = outputP := by rfl

theorem headSchemaP_holds (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source model) : planP.SchemaHolds planP.headSchema model := by
  rw [headSchemaP_exact]
  constructor
  · intro test member; cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    refine ⟨[(model 1).1,(model 2).1],rfl,?_⟩
    exact GeneralNominalState.normalized_models source model valid 0 (.pair (.var 1) (.var 2)) rfl
  · intro entry member
    simp only [headSchemaP,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · change GeneralNominalOriginTerms.Same model (.structural (.source 0) .pair 0) (.source (planP.binder 0))
      rw [binderP_zero]
      exact GeneralNominalStructuralReadback.actual_structural_readback
        (GeneralNominalSaturationState.initial context root) ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩
        (fun i : Fin 2 => if i.val = 0 then (1 : Fin 4) else (2 : Fin 4)) rfl ⟨0,by decide +kernel⟩ model
        ((GeneralNominalSaturationState.initial_models ..).mpr valid)
    · change GeneralNominalOriginTerms.Same model (.structural (.source 0) .pair 1) (.source (planP.binder 1))
      rw [binderP_one]
      exact GeneralNominalStructuralReadback.actual_structural_readback
        (GeneralNominalSaturationState.initial context root) ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩
        (fun i : Fin 2 => if i.val = 0 then (1 : Fin 4) else (2 : Fin 4)) rfl ⟨1,by decide +kernel⟩ model
        ((GeneralNominalSaturationState.initial_models ..).mpr valid)

theorem inputSchemaP_holds (model : GeneralNominalCommonBridge.Assignment) :
    planP.SchemaHolds (inputSchema packetP) model := by
  rw [inputSchemaP_exact]
  constructor <;> intro _ member <;> cases member

theorem childP_center (valid : childR.Signature roles) : ∀ index,
    (planP.childSite childR valid).center index = 1 := by
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  change planP.emittedCenter childR.id index.val (childR.arguments[index.val]'_) = 1
  simp only [zero,childR,List.getElem_cons_zero,Plan.emittedCenter,normalize]
  exact binderP_zero

theorem childP_arguments (valid : childR.Signature roles) : ∀ index,
    (planP.childSite childR valid).occurrence.demand.arguments index = (1,1) := by
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  simp [Plan.childSite,GeneralNominalFeedbackSites.clauseChild,GeneralNominalFeedbackSites.frame,
    GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDictionaryEmissionPlans.occurrence,GeneralNominalAllocation.frame,childR,zero,normalize]
  change (capture packetP).inputs 0 = _
  unfold capture
  rw [bindingsP]
  rfl

theorem childP_schema (valid : childR.Signature roles) :
    planP.schema (planP.childRequests childR valid) =
      { variables := [⟨0,.source 1,.actual⟩] } := by
  have requests : planP.childRequests childR valid = [⟨.var 0,1,.actual⟩] := by
    unfold Plan.childRequests
    change (List.ofFn fun index : Fin 1 => _) = _
    simp [List.ofFn_succ,childR]
    exact childP_center valid ⟨0,by change 0 < 1; omega⟩
  rw [requests]
  simp [Plan.schema,GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,
    normalize,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]

theorem childrenP_holds (model : GeneralNominalCommonBridge.Assignment) :
    ∀ clause ∈ packetP.declaration.requirements, ∀ valid : clause.Signature roles,
      (planP.childSite clause valid).Holds model ∧
        planP.SchemaHolds (planP.schema (planP.childRequests clause valid)) model := by
  intro clause member valid
  cases List.mem_singleton.mp member
  constructor
  · intro index
    unfold GeneralNominalCaptureMerges.Fits
    rw [childP_arguments,childP_center]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [childP_schema]
    constructor
    · intro test member; cases member
    · intro entry member; cases List.mem_singleton.mp member
      change GeneralNominalOriginTerms.Same model (.source 1) (.source (planP.binder 0))
      rw [binderP_zero]
      exact GeneralNominalOriginTerms.source_self _ _

theorem binderP_fits (model : GeneralNominalCommonBridge.Assignment) :
    ∀ name, name ∈ packetP.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed packetP name →
      GeneralNominalCaptureMerges.Fits model ((capture packetP).inputs name) (model (planP.binder name)).1 := by
  intro name member
  have two : name = 0 ∨ name = 1 := by
    rcases member with direct|⟨clause,member,needed⟩
    · simpa [packetP,p,Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] using direct
    · cases List.mem_singleton.mp member
      simp [childR,normalizeArgs,normalize,variablesArgs,Pattern.variables] at needed
      exact Or.inl needed
  rcases two with rfl|rfl
  · rw [binderP_zero]
    change GeneralNominalCaptureMerges.Fits model (GeneralNominalAllocation.capture source registry root.identity p.id packetP.bindings |>.inputs 0) _
    rw [bindingsP]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [binderP_one]
    change GeneralNominalCaptureMerges.Fits model (GeneralNominalAllocation.capture source registry root.identity p.id packetP.bindings |>.inputs 1) _
    rw [bindingsP]
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem centered_inputsP (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source model) : GeneralNominalCenteredSupport.Inputs planP model :=
  ⟨inputsP model,point_root_holds source.seed root (fun _ => rfl) model,binderP_fits model,
    headSchemaP_holds model valid,inputSchemaP_holds model,childrenP_holds model⟩

theorem namedSchemaP_holds (model : GeneralNominalCommonBridge.Assignment)
    (out : Equivalent (model 2).1 (model outputP).1) : planP.SchemaHolds (namedSchema packetP) model := by
  rw [schemaP_exact]
  constructor
  · intro test member; cases member
  · intro entry member
    simp only [schemaP,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · change GeneralNominalOriginTerms.Same model (.source 2) (.source (planP.binder 2))
      rw [binderP_two]
      exact ⟨⟨_,.source _⟩,⟨_,.source _⟩,by intro a b one two; cases one; cases two; exact out⟩
    · change GeneralNominalOriginTerms.Same model (.source outputP) (.source (planP.binder 2))
      rw [binderP_two]; exact GeneralNominalOriginTerms.source_self _ _

theorem planP_holds : planP.Holds witness := by
  have inputs := centered_inputsP witness witness_source
  exact ⟨packetP_holds,inputs.2.1,inputs.2.2.1,inputs.2.2.2.1,inputs.2.2.2.2.1,
    namedSchemaP_holds witness (by rw [witness_output]; exact ⟨subtype_refl _,subtype_refl _⟩),inputs.2.2.2.2.2⟩

theorem readsP : GeneralNominalSupport.readsMany source
    (GeneralNominalInspection.queries source interpretation p) [(0,0)] = [0,0] := by
  rw [queriesP]
  have atZero : source.view.heads 0 = .structural 0 (fun i => if i.val = 0 then 1 else 2) := rfl
  simp only [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads,atZero]
  change [0,0] ++ GeneralNominalSupport.readsMany source [.variables [0],.variables [1]] [(1,1),(2,2)] ++ [] = _
  simp [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads]

theorem source_headP : GeneralNominalSupport.Head source 0 (.structural .pair)
    (.normalized base 0 (.pair (.var 1) (.var 2))) :=
  .structural 0 0 (fun i => if i.val = 0 then 1 else 2) rfl

theorem source_readyP : GeneralNominalSupport.ReadyAt initialState.erased [] 0 :=
  GeneralNominalSupport.source_ready initialState.erased 0 (.structural .pair) _ _ source_headP source_headP []

theorem source_guardP : GeneralNominalSupportChoices.PacketGuard initialState.erased packetP [] := by
  have reads : ∀ slot ∈ GeneralNominalSupport.readsMany source
      (GeneralNominalInspection.queries source interpretation p) [(0,0)],
      GeneralNominalSupport.ReadyAt initialState.erased [] slot.val := by
    intro slot member
    rw [readsP] at member
    have zero : slot = (0 : Fin 4) := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
    subst slot
    exact source_readyP
  have roots : GeneralNominalSupport.Roots initialState.erased [] root := fun _ => source_readyP
  refine ⟨⟨(by intro _ member; cases member),roots,reads⟩,
    ⟨(by intro _ member; cases member),roots,?_⟩⟩
  intro declaration visible role bounds located
  have same := p_only declaration visible role
  subst declaration
  have exactBounds := Option.some.inj (located.symm.trans locatedP)
  subst bounds
  exact reads

theorem centered_decisionP : DecisionGuard registry initialState root := by
  apply GeneralNominalCenteredSupport.legacy_decision
  have ready : GeneralNominalSharedSupport.ReadyAt initialState.erased 0 :=
    ⟨.structural .pair,_,source_headP,GeneralNominalSharedSupport.source_head initialState.erased source_headP⟩
  refine ⟨fun _ => ready,?_⟩
  intro declaration visible role bounds located slot member
  have same := p_only declaration visible role
  subst declaration
  have exactBounds := Option.some.inj (located.symm.trans locatedP)
  subst bounds
  change slot ∈ GeneralNominalSupport.readsMany source (GeneralNominalInspection.queries source interpretation p) [(0,0)] at member
  rw [readsP] at member
  have zero : slot = (0 : Fin 4) := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  subst slot
  exact ready

theorem initial_no_cyclic (origin : Origin) : ¬ Cyclic initialState origin :=
  initial_acyclic context root initial_no_feedback origin

theorem inspectionP_count (candidate : Plan roles)
    (same : candidate.input = planP.input) (ctx : candidate.packet.context = context)
    (decl : candidate.packet.declaration = p)
    (located : arguments candidate.packet.context candidate.input.occurrence = some candidate.packet.bounds) :
    (inspection candidate).inspected.length = (inspection candidate).tests.length := by
  rcases candidate with ⟨⟨reg,ctxt,site,declaration,certified,bounds⟩,input,exactInput⟩
  change input = planP.input at same
  subst input
  change ctxt = context at ctx
  subst ctxt
  change declaration = p at decl
  subst declaration
  change arguments context root = some bounds at located
  have exactBounds := Option.some.inj (located.symm.trans locatedP)
  subst bounds
  unfold inspection
  change (inspectMany source (GeneralNominalInspection.queries source interpretation p) [(0,0)]
    (fun index => ((planP.input.observed.inputs[index]?).join)) 0).inspected.length =
      (inspectMany source (GeneralNominalInspection.queries source interpretation p) [(0,0)]
    (fun index => ((planP.input.observed.inputs[index]?).join)) 0).tests.length
  rw [queriesP]
  have atZero : source.view.heads 0 = .structural 0 (fun i => if i.val = 0 then 1 else 2) := rfl
  simp only [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_4,atZero]
  change ((Report.visit (0,0) (some (.source 0)) (.structural .pair)
    (inspectMany source [.variables [0],.variables [1]] [(1,1),(2,2)]
      (fun index => some (.structural (.source 0) .pair index)) 0)).append {}).inspected.length =
    ((Report.visit (0,0) (some (.source 0)) (.structural .pair)
    (inspectMany source [.variables [0],.variables [1]] [(1,1),(2,2)]
      (fun index => some (.structural (.source 0) .pair index)) 0)).append {}).tests.length
  simp [inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,Report.visit,Report.append]

theorem safeP : Safe initialState planP :=
  ⟨inspectionP_count planP rfl rfl rfl locatedP,fun entry _ => initial_no_cyclic entry.1⟩

theorem alternativesP : AlternativesSafe registry initialState planP.input := by
  intro candidate same registrySame contextSame visible role headReady located
  have exactRole : candidate.packet.declaration.role = root.demand.role := role
  have declarationSame := p_only candidate.packet.declaration visible exactRole
  have argumentsSame : arguments candidate.packet.context candidate.input.occurrence = some candidate.packet.bounds := by
    rw [same]
    exact located
  exact ⟨inspectionP_count candidate same contextSame declarationSame argumentsSame,
    fun entry _ => initial_no_cyclic entry.1⟩

theorem guardP : PacketGuard initialState planP [] := by
  refine ⟨List.mem_singleton_self _,GeneralNominalValueSupport.source_packet _ _ source_guardP,
    centered_decisionP,safeP,alternativesP,?_,witness,?_,planP_holds⟩
  · constructor
    · rintro ⟨site,member,same,index,cyclic⟩; exact initial_no_cyclic _ cyclic
    · rintro ⟨plan,member,same,reg,ctx,visible,role,headReady,located,entry,present,cyclic⟩
      exact initial_no_cyclic _ cyclic
  · apply (point_initial_models context root (fun _ => rfl) witness).mpr
    exact witness_source

abbrev childSignature : childR.Signature roles := p_checked.signature.2.2.2 childR (List.mem_singleton_self _)
abbrev emittedChild : Site roles := planP.childSite childR childSignature

theorem novelP : ¬ GeneralNominalFeedbackSteps.Committed initialState.erased.current packetP := by
  intro committed
  have member : emittedChild.occurrence ∈ packetP.children :=
    GeneralNominalCenteredProgress.clause_child_member planP childR (List.mem_singleton_self _) childSignature
  exact List.not_mem_nil (committed.2 emittedChild.occurrence member)

theorem stepP : Step registry root initialState afterP :=
  ⟨root,.root,.install planP [] enabledP novelP guardP⟩



abbrev refreshedAtoms : List (PresenceNormalForm.Atom (Fin 5)) :=
  equationAtoms 0 (.pair (.var 1) (.var 2)) ++ equationAtoms 1 (.pair (.var 2) (.var 2)) ++
    equationAtoms 3 (.base .int) ++ equationAtoms 4 (.var 2)
abbrev refreshedIdentifiers (slot : Fin 5) : Nat := if slot.val = 4 then outputP else slot.val
abbrev refreshedRawShapes : Fin 1 → GeneralSourceState.Shape 5 := fun _ => .pair
abbrev refreshedRawHeads : Fin 5 → GeneralSourceState.Head refreshedRawShapes := fun slot =>
  if slot = 0 then .structural 0 (fun i => if i.val = 0 then 1 else 2) else
  if slot = 1 then .structural 0 (fun _ => 4) else
  if slot = 3 then .scalar .int else .unresolved

abbrev refreshedBase : GeneralSourceState.State where
  slots := 5
  source := refreshedIdentifiers
  source_injective := by
    intro first last equal
    have fresh := outputP_large
    have one := first.isLt
    have two := last.isLt
    apply Fin.ext
    dsimp only [refreshedIdentifiers] at equal
    split at equal <;> split at equal <;> omega
  rowSource := refreshedIdentifiers
  ordinary := refreshedAtoms
  kinds := 1
  shapes := refreshedRawShapes
  shapes_injective := by intro a b _; exact Subsingleton.elim a b
  heads := refreshedRawHeads
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    have facts : PresenceNormalForm.All Common.model assignment (equationAtoms 0 (.pair (.var 1) (.var 2))) ∧
      PresenceNormalForm.All Common.model assignment (equationAtoms 1 (.pair (.var 2) (.var 2))) ∧
      PresenceNormalForm.All Common.model assignment (equationAtoms 3 (.base .int)) ∧
      PresenceNormalForm.All Common.model assignment (equationAtoms 4 (.var 2)) := by
      simpa only [refreshedAtoms,PresenceNormalForm.all_append,and_assoc] using valid
    by_cases zero : slot = 0
    · subst slot
      have equal : (.pair (.var 1) (.var 2) : TyTerm (Fin 5)) = term := by
        simpa [refreshedRawHeads,GeneralSourceState.Head.equation,refreshedRawShapes,GeneralSourceState.Shape.term] using recorded
      subst term; exact (equationAtoms_exact ..).mp facts.1
    · by_cases one : slot = 1
      · subst slot
        have equal : (.pair (.var 4) (.var 4) : TyTerm (Fin 5)) = term := by
          simpa [refreshedRawHeads,GeneralSourceState.Head.equation,refreshedRawShapes,GeneralSourceState.Shape.term] using recorded
        subst term
        have old := (equationAtoms_exact ..).mp facts.2.1
        have alias := (equationAtoms_exact ..).mp facts.2.2.2
        exact Common.equivalent_trans old ((CommonCanonicalShapes.pair_equivalent_iff ..).mpr
          ⟨⟨alias.2,alias.1⟩,⟨alias.2,alias.1⟩⟩)
      · by_cases three : slot = 3
        · subst slot
          have equal : (.base .int : TyTerm (Fin 5)) = term := by
            simpa [refreshedRawHeads,GeneralSourceState.Head.equation] using recorded
          subst term; exact (equationAtoms_exact ..).mp facts.2.2.1
        · simp [refreshedRawHeads,zero,one,three,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by intro _ _ _ member; cases member

abbrev refreshedView : GeneralNormalizedObservation.Snapshot refreshedBase where
  kinds := 1
  shapes := fun _ => .pair
  shapes_injective := by intro a b _; exact Subsingleton.elim a b
  canonical := by intro _; trivial
  heads := fun slot => if slot = 0 then .structural 0 (fun i => if i.val = 0 then 1 else 2) else
    if slot = 1 then .structural 0 (fun _ => 4) else
    if slot = 3 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have equal : (.pair (.var 1) (.var 2) : TyTerm (Fin 5)) = term := by
        simpa [GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Shape.term] using recorded
      subst term; exact .head rfl
    · by_cases one : slot = 1
      · subst slot
        have equal : (.pair (.var 4) (.var 4) : TyTerm (Fin 5)) = term := by
          simpa [GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Shape.term] using recorded
        subst term; exact .head rfl
      · by_cases three : slot = 3
        · subst slot
          have equal : (.base .int : TyTerm (Fin 5)) = term := by
            simpa [GeneralNormalizedObservation.Head.term] using recorded
          subst term; exact .head rfl
        · simp [zero,one,three,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev refreshedSource : GeneralNominalState.State where
  base := refreshedBase
  view := refreshedView
  constructors := constructors
  nominals := fun _ => none
  catalogue := by intro _ _ impossible; cases impossible
  bodies_opaque := by intro _ _ impossible; cases impossible
  seed := 3
  allocated := packetP.privateContext.state.allocated
  reserved := packetP.privateContext.state.reserved
  ordinary := packetP.privateContext.state.ordinary
abbrev refreshedContext : GeneralNominalCandidates.Context := ⟨refreshedSource,interpretation⟩
noncomputable abbrev refreshed := GeneralNominalCenteredSteps.refresh afterP refreshedContext

abbrev refreshEmbed (slot : Fin 4) : Fin 5 := ⟨slot.val,by omega⟩
theorem refresh_source_embed (slot : Fin 4) : refreshedIdentifiers (refreshEmbed slot) = slot.val := by
  have small := slot.isLt
  simp [refreshedIdentifiers,show slot.val ≠ 4 by omega]

theorem refresh_raw_known (slot : Fin 4) (known : base.graph slot ≠ .unresolved) :
    refreshedBase.graph (refreshEmbed slot) ≠ .unresolved := by
  by_cases zero : slot = 0
  · subst slot; intro impossible; cases impossible
  · by_cases one : slot = 1
    · subst slot; intro impossible; cases impossible
    · apply False.elim
      apply known
      simp [GeneralSourceState.State.graph,base,rawHeads,zero,one,GeneralSourceState.Head.node]

theorem refresh_view_known (slot : Fin 4) (known : source.view.graph slot ≠ .unresolved) :
    refreshedView.graph (refreshEmbed slot) ≠ .unresolved := by
  by_cases zero : slot = 0
  · subst slot; intro impossible; cases impossible
  · by_cases one : slot = 1
    · subst slot; intro impossible; cases impossible
    · apply False.elim
      apply known
      simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node,
        source,GeneralNominalState.embed,view,zero,one]

noncomputable def refreshRefines : GeneralNominalRefinements.Refines afterP.erased.current.context.state refreshedSource where
  base := {
    embed := refreshEmbed
    source := refresh_source_embed
    rowSource := refresh_source_embed
    ordinary := by
      intro atom member
      change atom ∈ atoms at member
      simp only [atoms,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with ((rfl|rfl)|(rfl|rfl))|(rfl|rfl)
      all_goals simp [refreshedBase,refreshedAtoms,equationAtoms,PresenceNormalForm.Atom.rename,TyTerm.rename,refreshEmbed]
      all_goals rfl
    known := refresh_raw_known
    intervals := by intro bounds member; cases member }
  heads := by
    change ∀ (slot : Fin 4) (term : TyTerm (Fin 4)), (rawHeads slot).equation = some term →
      GeneralNormalizedObservation.Rewrites refreshedBase (.var (refreshEmbed slot)) (term.rename refreshEmbed)
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have equal : (.pair (.var 1) (.var 2) : TyTerm (Fin 4)) = term := by
        simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
      subst term
      apply GeneralNormalizedObservation.Rewrites.ordinary
      all_goals simp [refreshedBase,refreshedAtoms,equationAtoms,TyTerm.rename,refreshEmbed]
    · by_cases one : slot = 1
      · subst slot
        have equal : (.pair (.var 2) (.var 2) : TyTerm (Fin 4)) = term := by
          simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
        subst term
        apply GeneralNormalizedObservation.Rewrites.ordinary
        all_goals simp [refreshedBase,refreshedAtoms,equationAtoms,TyTerm.rename,refreshEmbed]
      · simp [rawHeads,zero,one,GeneralSourceState.Head.equation] at recorded
  nominals := by intro slot desc recorded; cases recorded
  ordinary := fun _ member => member
  known := by
    rintro identity ⟨slot,equal,head|⟨descriptor,recorded⟩⟩
    · exact ⟨refreshEmbed slot,(refresh_source_embed slot).trans equal,Or.inl (refresh_view_known slot head)⟩
    · cases recorded
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl



theorem outputP_supported : outputP ∈ GeneralNominalState.sources afterP.erased.current.context.state :=
  (GeneralNominalSourceFormation.installation_reserves packetP
    (GeneralNominalAllocation.origin root.identity p.id 2 2 0) (by decide +kernel)).1

theorem refreshed_support : ∀ identity ∈ GeneralNominalState.sources refreshedSource,
    identity ∈ GeneralNominalState.sources afterP.erased.current.context.state := by
  intro identity member
  simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
  rcases member with ((type|row)|reserved)|ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp type
    change refreshedIdentifiers slot = identity at equal
    subst identity
    by_cases four : slot.val = 4
    · simpa only [refreshedIdentifiers,ite_eq_left four,GeneralNominalState.sources,List.mem_append] using outputP_supported
    · have small : slot.val < 4 := by have h := slot.isLt; omega
      rw [show refreshedIdentifiers slot = slot.val by simp [refreshedIdentifiers,four]]
      exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,small⟩,rfl⟩)))
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp row
    change refreshedIdentifiers slot = identity at equal
    subst identity
    by_cases four : slot.val = 4
    · simpa only [refreshedIdentifiers,ite_eq_left four,GeneralNominalState.sources,List.mem_append] using outputP_supported
    · have small : slot.val < 4 := by have h := slot.isLt; omega
      rw [show refreshedIdentifiers slot = slot.val by simp [refreshedIdentifiers,four]]
      exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,small⟩,rfl⟩)))
  · exact Or.inl (Or.inr reserved)
  · exact Or.inr ordinary

theorem afterP_output (model : GeneralNominalCommonBridge.Assignment) (valid : Models afterP model) :
    Equivalent (model 2).1 (model outputP).1 := by
  have branch := ((install_models (state := initialState) (plan := planP) (support := []) rfl model).mp valid).2
  have output := ((packet_exact packetP model).mp branch.1).2.2
  unfold Outputs at output
  rw [schemaP_exact] at output
  exact (output.2.1 ⟨2,.source 2,.actual⟩ (List.mem_cons_self ..)).2 _ (.source 2)

theorem refreshed_exact (model : GeneralNominalCommonBridge.Assignment) (valid : Models afterP model) :
    GeneralNominalState.Models refreshedSource model := by
  have prior := ((install_models (state := initialState) (plan := planP) (support := []) rfl model).mp valid).1
  have old := (point_initial_models context root (fun _ => rfl) model).mp prior
  have zero : Equivalent (model 0).1 (pair (model 1).1 (model 2).1) := old.1.2.1 0 _ rfl
  have one : Equivalent (model 1).1 (pair (model 2).1 (model 2).1) := old.1.2.1 1 _ rfl
  have three : Equivalent (model 3).1 (.base .int) := by
    constructor
    · exact old.1.1 (.tyLe (.var 3) (.base .int)) (by simp [source,GeneralNominalState.embed,base,atoms,equationAtoms])
    · exact old.1.1 (.tyLe (.base .int) (.var 3)) (by simp [source,GeneralNominalState.embed,base,atoms,equationAtoms])
  have out := afterP_output model valid
  have actualPair : Equivalent (model 1).1 (pair (model outputP).1 (model outputP).1) :=
    ⟨subtype_trans one.1 ((common_pair_iff ..).mpr ⟨out.1,out.1⟩),
      subtype_trans ((common_pair_iff ..).mpr ⟨out.2,out.2⟩) one.2⟩
  refine ⟨⟨?_,?_,?_⟩,?_,valid.1.1.2.2⟩
  · intro atom member
    change atom ∈ refreshedAtoms at member
    simp only [refreshedAtoms,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (((rfl|rfl)|(rfl|rfl))|(rfl|rfl))|(rfl|rfl)
    · exact zero.1
    · exact zero.2
    · exact one.1
    · exact one.2
    · exact three.1
    · exact three.2
    · exact out.2
    · exact out.1
  · intro slot term recorded
    change (refreshedRawHeads slot).equation = some term at recorded
    by_cases atZero : slot = 0
    · subst slot
      have equal : (.pair (.var 1) (.var 2) : TyTerm (Fin 5)) = term := by
        simpa [refreshedRawHeads,GeneralSourceState.Head.equation,refreshedRawShapes,GeneralSourceState.Shape.term] using recorded
      subst term; exact zero
    · by_cases atOne : slot = 1
      · subst slot
        have equal : (.pair (.var 4) (.var 4) : TyTerm (Fin 5)) = term := by
          simpa [refreshedRawHeads,GeneralSourceState.Head.equation,refreshedRawShapes,GeneralSourceState.Shape.term] using recorded
        subst term; exact actualPair
      · by_cases atThree : slot = 3
        · subst slot
          have equal : (.base .int : TyTerm (Fin 5)) = term := by
            simpa [refreshedRawHeads,GeneralSourceState.Head.equation] using recorded
          subst term; exact three
        · simp [refreshedRawHeads,atZero,atOne,atThree,GeneralSourceState.Head.equation] at recorded
  · intro bounds member; cases member
  · intro slot desc recorded; cases recorded

noncomputable def refreshCertificate : Refresh afterP refreshedContext :=
  ⟨refreshRefines,rfl,refreshed_exact,refreshed_support⟩

theorem progress_unknown : ¬ GeneralNominalState.Known afterP.erased.current.context.state 3 := by
  rintro ⟨slot,equal,head|⟨descriptor,recorded⟩⟩
  · have same : slot = (3 : Fin 4) := Fin.ext equal
    subst slot
    exact head rfl
  · cases recorded

theorem progress_known : GeneralNominalState.Known refreshedSource 3 :=
  ⟨3,rfl,Or.inl (by intro impossible; cases impossible)⟩

theorem refreshStep : Step registry root afterP refreshed := by
  refine ⟨root,.root,.refresh root refreshedContext refreshCertificate 3 ?_ progress_unknown progress_known⟩
  exact GeneralNominalAllocationSupport.slot_source afterP.erased.current.context.state (3 : Fin 4)

theorem refreshed_reachable : B4Target.Steps (Step registry root) initialState refreshed :=
  .tail (.tail .refl stepP) refreshStep

noncomputable abbrev rawR := GeneralNominalSharedEmission.childSite packetP emittedChild.occurrence
noncomputable abbrev packetR : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,refreshedContext,rawR,r,r_checked,[(1,1)]⟩
noncomputable abbrev planR : Plan roles := ⟨packetR,emittedChild,rfl⟩
noncomputable abbrev afterR := install refreshed planR []

abbrev reportR : Report refreshedSource where
  captures := [⟨0,(4,4),none⟩,⟨1,(4,4),none⟩]
  inspected := [(1,1)]
  checked := [(1,1),(1,1),(4,4),(4,4)]

theorem queriesR : GeneralNominalInspection.queries refreshedSource interpretation r =
    [.node .pair [.variables [0],.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,r,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]
theorem reportR_exact : GeneralNominalPacketSupport.report packetR = reportR := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  have atOne : refreshedSource.view.heads 1 = .structural 0 (fun _ => 4) := rfl
  change { inspectMany refreshedSource (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)]
    (fun _ => none) 0 with checked := [(1,1)] ++
    (inspectMany refreshedSource (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)] (fun _ => none) 0).checked } = _
  rw [queriesR]
  simp only [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_4,atOne]
  change { (Report.visit (1,1) none (.structural .pair)
    (inspectMany refreshedSource [.variables [0],.variables [1]] [(4,4),(4,4)] (fun _ => none) 0)).append {} with
    checked := [(1,1)] ++ ((Report.visit (1,1) none (.structural .pair)
    (inspectMany refreshedSource [.variables [0],.variables [1]] [(4,4),(4,4)] (fun _ => none) 0)).append {}).checked } = _
  simp [inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,Report.append,Report.visit,reportR]
theorem bindingsR : packetR.bindings = [(0,(outputP,outputP)),(1,(outputP,outputP))] := by
  change bindings refreshedSource (GeneralNominalPacketSupport.report packetR) = _
  rw [reportR_exact]; rfl

theorem r_sorted : GeneralCanonicalChildOrder.canonicalDeclaration r = r := by decide +kernel

theorem locatedR : arguments refreshedContext emittedChild.occurrence = some [(1,1)] := by
  change arguments refreshedContext (planP.childSite childR childSignature).occurrence = _
  decide +kernel

theorem readsR : GeneralNominalSupport.readsMany refreshedSource
    (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)] = [1,1] := by
  rw [queriesR]
  have atOne : refreshedSource.view.heads 1 = .structural 0 (fun _ => 4) := rfl
  simp only [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads,atOne]
  change [1,1] ++ GeneralNominalSupport.readsMany refreshedSource [.variables [0],.variables [1]] [(4,4),(4,4)] ++ [] = _
  simp [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads]

theorem current_headR : GeneralNominalSupport.Head refreshedSource 1 (.structural .pair)
    (.normalized refreshedBase 1 (.pair (.var 4) (.var 4))) :=
  .structural 1 0 (fun _ => 4) rfl

theorem old_headR : GeneralNominalSupport.Head source 1 (.structural .pair)
    (.normalized base 1 (.pair (.var 2) (.var 2))) :=
  .structural 1 0 (fun _ => 2) rfl

theorem readyR : GeneralNominalSupport.ReadyAt refreshed.erased [] 1 :=
  GeneralNominalSupport.source_ready refreshed.erased 1 (.structural .pair) _ _ old_headR current_headR []

def bad : GeneralNominalCommonBridge.Assignment := fun identity =>
  if identity = outputP then (pair (.base .int) (.base .int), Common.rowEmpty) else witness identity

theorem bad_old (identity : Nat) (small : identity ≤ 3) : bad identity = witness identity := by
  have different : identity ≠ outputP := by have large := outputP_large; omega
  simp [bad,different]

theorem bad_source : GeneralNominalState.Models source bad := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro atom member
    simp only [base,atoms,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ((rfl|rfl)|(rfl|rfl))|(rfl|rfl)
    · change Subtype (bad 0).1 (pair (bad 1).1 (bad 2).1)
      rw [bad_old 0 (by decide),bad_old 1 (by decide),bad_old 2 (by decide)]
      exact subtype_refl _
    · change Subtype (pair (bad 1).1 (bad 2).1) (bad 0).1
      rw [bad_old 0 (by decide),bad_old 1 (by decide),bad_old 2 (by decide)]
      exact subtype_refl _
    · change Subtype (bad 1).1 (pair (bad 2).1 (bad 2).1)
      rw [bad_old 1 (by decide),bad_old 2 (by decide)]
      exact subtype_refl _
    · change Subtype (pair (bad 2).1 (bad 2).1) (bad 1).1
      rw [bad_old 1 (by decide),bad_old 2 (by decide)]
      exact subtype_refl _
    · change Subtype (bad 3).1 (.base .int)
      rw [bad_old 3 (by decide)]
      exact subtype_refl _
    · change Subtype (.base .int) (bad 3).1
      rw [bad_old 3 (by decide)]
      exact subtype_refl _
  · intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have eq : (.pair (.var 1) (.var 2) : TyTerm (Fin 4)) = term := by
        simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
      subst term
      change Equivalent (bad 0).1 (pair (bad 1).1 (bad 2).1)
      rw [bad_old 0 (by decide),bad_old 1 (by decide),bad_old 2 (by decide)]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · by_cases one : slot = 1
      · subst slot
        have eq : (.pair (.var 2) (.var 2) : TyTerm (Fin 4)) = term := by
          simpa [rawHeads,GeneralSourceState.Head.equation,rawShapes,GeneralSourceState.Shape.term] using recorded
        subst term
        change Equivalent (bad 1).1 (pair (bad 2).1 (bad 2).1)
        rw [bad_old 1 (by decide),bad_old 2 (by decide)]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · simp [base,rawHeads,zero,one,GeneralSourceState.Head.equation] at recorded
  · intro bounds member; cases member
  · intro slot desc recorded; cases recorded
  · intro atom member; cases member

theorem bad_coarse : GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites [] bad := by
  refine ⟨bad_source,?_,?_⟩
  · intro site member
    have same := List.mem_singleton.mp member
    subst site
    exact point_root_holds source.seed root (fun _ => rfl) bad
  · intro fact member; cases member

theorem current_headR_not_source :
    ¬ (GeneralCanonicalObservations.Observation.normalized refreshedBase 1 (.pair (.var 4) (.var 4))).Holds bad := by
  intro holds
  change Equivalent (bad 1).1 (pair (bad outputP).1 (bad outputP).1) at holds
  rw [bad_old 1 (by decide)] at holds
  have first := ((common_pair_iff ..).mp holds.1).1
  change Subtype (.base .int) (bad outputP).1 at first
  have different : bad outputP = (pair (.base .int) (.base .int),Common.rowEmpty) := by simp [bad]
  rw [different] at first
  exact GeneralNominalBranchingReadback.scalar_not_pair _ _ _ first

theorem no_empty_readbackR :
    ¬ GeneralNominalCenteredSupport.Readback refreshed.erased refreshed.sourceSites [] planR := by
  intro readback
  have member : (1 : Fin refreshedSource.base.slots) ∈ GeneralNominalSupport.readsMany refreshedSource
      (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)] := by
    rw [readsR]; exact List.mem_cons_self ..
  exact current_headR_not_source (readback 1 member _ _ current_headR bad bad_coarse)

abbrev schemaR : GeneralNominalMaterialization.Schema where
  variables := [⟨0,.source outputP,.actual⟩]

theorem rootR_outputs : emittedChild.occurrence.demand.outputs = [⟨0,outputP⟩] := by rfl

theorem schemaR_exact : namedSchema packetR = schemaR := by
  unfold namedSchema GeneralNominalRecursiveCandidates.generated
  change GeneralNominalMaterialization.generated refreshedSource interpretation
    (GeneralNominalMaterialization.requests refreshedSource registry emittedChild.occurrence r r_checked packetR.bindings) = _
  rw [bindingsR]
  unfold GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,r_sorted]
  simp only [GeneralNominalMaterialization.rootRequests,rootR_outputs]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,r,childS,
    List.ofFn_succ,normalize,normalizeArgs,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
    GeneralDeclarationDemands.outputTarget,GeneralDeclarationDemands.inputInterval,
    GeneralDeclarationDemands.childDemand,Declaration.outputNames,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.allocation,GeneralNominalAllocation.occurrences,schemaR]

theorem inputSchemaR_exact : inputSchema packetR = {} := by
  unfold inputSchema inputRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,r_sorted]
  simp [packetR,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,r,childS,
    List.ofFn_succ,GeneralNominalMaterialization.inputRequests,
    GeneralDeclarationDemands.childDemand,roles,GeneralNominalProvenanceDeclarations.bareRole,
    normalize,GeneralNominalMaterialization.generated]

theorem projectionR (model : GeneralNominalCommonBridge.Assignment) : ProjectionModels refreshedSource reportR model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member; cases member
  · intro test member; cases member
  · intro first one last two same ref recorded actual seen
    simp only [reportR,List.mem_cons,List.not_mem_nil,or_false] at one
    rcases one with rfl|rfl <;> cases recorded
  · intro first present last two same a b one two x y hx hy
    simp only [reportR,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl <;> cases one

theorem ordinaryR (model : GeneralNominalCommonBridge.Assignment) : Ordinary packetR model := by
  refine ⟨?_,?_,?_⟩
  · intro first one last two same
    rw [bindingsR] at one two
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl|rfl <;> rcases two with rfl|rfl
    all_goals first | exact subtype_refl _ | cases same
  · have empty : GeneralNominalAllocation.merges refreshedSource registry emittedChild.occurrence.identity r packetR.bindings = [] := by
      rw [bindingsR]; rfl
    change PresenceNormalForm.All _ _ (GeneralNominalAllocation.merges refreshedSource registry emittedChild.occurrence.identity r packetR.bindings)
    rw [empty]; exact PresenceNormalForm.all_nil _ _
  · change PresenceNormalForm.All _ _ (selfChecks refreshedSource (GeneralNominalPacketSupport.report packetR))
    rw [reportR_exact]
    intro atom member
    simp only [selfChecks,reportR,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact subtype_refl _

theorem inputsR (model : GeneralNominalCommonBridge.Assignment) : Inputs packetR model := by
  refine ⟨ordinaryR model,?_,?_⟩
  · change ProjectionModels refreshedSource (GeneralNominalPacketSupport.report packetR) model
    rw [reportR_exact]; exact projectionR model
  · rw [inputSchemaR_exact]
    exact GeneralNominalMaterialization.empty_models ..

theorem outputsR (model : GeneralNominalCommonBridge.Assignment) : Outputs packetR model := by
  unfold Outputs
  rw [schemaR_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member; cases member
  · intro entry member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    have captured : (capture packetR).inputs 0 = (outputP,outputP) := by
      unfold capture
      rw [bindingsR]; rfl
    change GeneralNominalCaptureMerges.Fits model ((capture packetR).inputs 0) (model outputP).1
    rw [captured]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two same firstActual lastActual a b ha hb
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    cases ha; cases hb
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member captured present same actual origin recorded a b ha hb
    change captured ∈ (GeneralNominalPacketSupport.report packetR).captures at present
    rw [reportR_exact] at present
    simp only [reportR,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl <;> cases recorded

theorem witness_afterP : Models afterP witness :=
  (install_models rfl witness).mpr ⟨(point_initial_models context root (fun _ => rfl) witness).mpr witness_source,planP_holds⟩

theorem witness_refreshed : Models refreshed witness := (refresh_models refreshCertificate witness).mpr witness_afterP

theorem packetR_holds : packetR.Holds witness :=
  (packet_exact packetR witness).mpr ⟨witness_refreshed.1.1,inputsR witness,outputsR witness⟩

theorem privateP_ordinary : packetP.privateContext.state.ordinary =
    [.tyLe (.var 1) (.var 1),.tyLe (.var 2) (.var 2),
     .tyLe (.var 0) (.var 0),.tyLe (.var 0) (.var 0),.tyLe (.var 1) (.var 1),.tyLe (.var 2) (.var 2)] := by
  change (source.ordinary ++
    (GeneralNominalAllocation.cross packetP.bindings ++ GeneralNominalAllocation.merges source registry root.identity p packetP.bindings)) ++
    selfChecks source (GeneralNominalPacketSupport.report packetP) = _
  rw [bindingsP,reportP_exact]
  rfl

theorem freshR : GeneralNominalAllocation.Fresh refreshedSource registry emittedChild.occurrence.identity := by
  intro key member collision
  have old := refreshed_support _ collision
  change GeneralNominalAllocation.source source registry emittedChild.occurrence.identity key ∈
    List.ofFn base.source ++ List.ofFn base.rowSource ++
      ([] ++ GeneralNominalAllocation.reserved source registry root.identity ++ []) ++
      packetP.privateContext.state.ordinary.flatMap GeneralNominalState.atomSources at old
  rw [privateP_ordinary] at old
  simp only [List.nil_append,List.append_nil,List.mem_append,List.mem_ofFn] at old
  rcases old with ((⟨slot,same⟩|⟨slot,same⟩)|reserved)|other
  · have above := GeneralNominalIdentities.source_above_seed source.seed key
    change slot.val = GeneralNominalIdentities.source source.seed key at same
    have less := slot.isLt
    change _ < 4 at less
    change 3 < _ at above
    omega
  · have above := GeneralNominalIdentities.source_above_seed source.seed key
    change slot.val = GeneralNominalIdentities.source source.seed key at same
    have less := slot.isLt
    change _ < 4 at less
    change 3 < _ at above
    omega
  · obtain ⟨original,present,same⟩ := List.mem_map.mp reserved
    have equal := (GeneralNominalIdentities.source_identity source.seed original key).mp same
    subst key
    change original ∈ [] ++ GeneralNominalAllocation.keys registry root.identity
    exact List.mem_append_right _ present
  · have above := GeneralNominalIdentities.source_above_seed source.seed key
    simp only [List.flatMap_cons,List.flatMap_nil,GeneralNominalState.atomSources,GeneralNominalState.typeSources,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at other
    change 3 < GeneralNominalAllocation.source source registry emittedChild.occurrence.identity key at above
    omega

theorem linkedR : GeneralNominalState.Linked refreshedSource emittedChild.occurrence.demand := by
  constructor
  · intro index
    have same := childP_arguments childSignature index
    rw [same]
    have member : 1 ∈ GeneralNominalState.sources refreshedSource :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨1,rfl⟩)))
    exact ⟨member,member⟩
  · intro output member
    rw [rootR_outputs] at member
    cases List.mem_singleton.mp member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨4,rfl⟩)))

theorem preparedR : Prepared registry refreshedContext emittedChild.occurrence r r_checked := by
  refine ⟨initial_source.metadata,linkedR,freshR,[(1,1)],locatedR,?_,?_,witness,packetR_holds⟩
  · change Finished (GeneralNominalPacketSupport.report packetR)
    rw [reportR_exact]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro out member
      rw [rootR_outputs] at member
      cases List.mem_singleton.mp member
      exact ⟨⟨201,0,.var 0⟩,List.mem_singleton_self _,rfl⟩
    · change (namedSchema packetR).unknown = false
      rw [schemaR_exact]

theorem refreshed_smaller (first last : Fin refreshedSource.base.slots)
    (edge : GeneralSourceK2.Child refreshedSource.view first last) :
    height (refreshedSource.base.source last) < height (refreshedSource.base.source first) := by
  obtain ⟨kind,children,recorded,index,rfl⟩ := edge
  by_cases zero : first = 0
  · subst first
    change GeneralNormalizedObservation.Head.structural 0 (fun i => if i.val = 0 then 1 else 2) = _ at recorded
    cases recorded
    by_cases atZero : index.val = 0
    · simp [height,witnessTree,atZero,GeneralNominalBranchingReadback.Tree.mass,refreshedIdentifiers]
    · simp [height,witnessTree,atZero,GeneralNominalBranchingReadback.Tree.mass,refreshedIdentifiers]
  · by_cases one : first = 1
    · subst first
      change GeneralNormalizedObservation.Head.structural 0 (fun _ => 4) = _ at recorded
      cases recorded
      have notZero : outputP ≠ 0 := by have h := outputP_large; omega
      have notOne : outputP ≠ 1 := by have h := outputP_large; omega
      change height outputP < height 1
      simp [height,witnessTree,GeneralNominalBranchingReadback.Tree.mass,notZero,notOne]
    · by_cases three : first = 3
      · subst first
        change GeneralNormalizedObservation.Head.scalar .int = _ at recorded
        cases recorded
      · have absent : refreshedSource.view.heads first = .deferred .unresolved := by
          change (if first = 0 then _ else if first = 1 then _ else if first = 3 then _ else _) = _
          rw [ite_eq_right zero,ite_eq_right one,ite_eq_right three]
        rw [absent] at recorded; cases recorded

theorem refreshed_no_raw (slot : Fin refreshedSource.base.slots) :
    ¬ GeneralNominalCycleK2.Cycle refreshedSource slot :=
  raw_acyclic refreshedSource (fun _ => rfl) refreshed_smaller slot

theorem refreshed_no_feedback (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle refreshed.erased.current identity :=
  feedback_acyclic refreshed.erased.current witness_refreshed.1 refreshed_smaller identity

theorem no_rootR : ¬ GeneralNominalFeedbackK2.RootK2 refreshed.erased.current emittedChild.occurrence := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact refreshed_no_raw slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact refreshed_no_feedback _ cycle

theorem no_candidateR : ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed.erased.current emittedChild.occurrence := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact refreshed_no_raw visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact refreshed_no_feedback _ cycle

theorem rootR_ready : ¬ GeneralNominalState.RootPending refreshedSource emittedChild.occurrence.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  rw [childP_arguments childSignature index]
  refine ⟨1,rfl,Or.inl ?_⟩
  intro impossible
  cases impossible

theorem r_only (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (role : declaration.role = emittedChild.occurrence.demand.role) : declaration = r := by
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl|rfl
  · cases role
  · rfl

theorem survivorR : Survivor registry refreshedContext emittedChild.occurrence r.id packetR.children :=
  ⟨rootR_ready,r,by simp [registry],r_checked,rfl,rfl,[(1,1)],locatedR,preparedR,rfl⟩

theorem selectedR : GeneralNominalFeedbackK2.Local registry refreshed.erased.current emittedChild.occurrence
    (.selected r.id packetR.children) := by
  refine .selected ⟨rootR_ready,no_rootR,no_candidateR,?_⟩ ⟨survivorR,?_⟩
  · rintro (pending|⟨_,legacy⟩)
    · obtain ⟨_,declaration,visible,certified,role,_,missing⟩ := pending
      have same := r_only declaration visible role
      subst declaration
      exact missing preparedR
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩|⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · exact no_legacy refreshedSource (fun _ => rfl) refreshed_smaller slot cycle
      · exact no_legacy refreshedSource (fun _ => rfl) refreshed_smaller visited.1 cycle
  · intro key kids found
    have copied := found
    obtain ⟨_,declaration,visible,certified,identity,role,_⟩ := found
    have same := r_only declaration visible role
    subst declaration; subst key
    exact ⟨rfl,survivor_children_functional registry checked refreshedContext emittedChild.occurrence r.id kids packetR.children copied survivorR⟩

theorem refreshed_alias_eq {first last : Nat} (alias : GeneralNominalSaturationState.Alias refreshed.erased.current first last) : first = last := by
  induction alias with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem child_identity_not_root : emittedChild.occurrence.identity ≠ root.identity := by
  have larger := GeneralNominalIdentities.source_above_invocation source.seed
    (GeneralNominalAllocation.origin root.identity p.id 6 childR.id 0)
  exact Nat.ne_of_gt larger

theorem childrenP_exact : packetP.children = [emittedChild.occurrence] := by
  change (GeneralCanonicalChildOrder.canonicalEmit root.identity p p_checked
    (GeneralNominalPacketSupport.capture packetP)
    (GeneralNominalAllocation.allocation source registry root.identity p.id)).map _ = _
  simp only [GeneralCanonicalChildOrder.canonicalEmit,p_sorted]
  rfl

theorem refreshed_sites : refreshed.erased.current.sites = [GeneralNominalDemandMerging.pointSite root,rawR] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ packetP.children.map (GeneralNominalSharedEmission.childSite packetP) = _
  rw [childrenP_exact]; rfl

theorem compatibleR : GeneralNominalCycleSteps.ChoiceCompatible refreshed.erased.current packetR := by
  intro prior member same
  cases List.mem_singleton.mp member
  exact False.elim (child_identity_not_root (refreshed_alias_eq same))

theorem mergesClosedR : GeneralNominalCycleSteps.MergesClosed refreshed.erased.current packetR.site := by
  intro other member same
  rw [refreshed_sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · cases same.1
  · exact .refl _

theorem feedbackMergesClosedR : GeneralNominalFeedbackSteps.MergesClosed refreshed.erased.current packetR.site := by
  intro other member same
  rw [refreshed_sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · cases same.1
  · exact .refl _

theorem jointR : GeneralNominalJointCandidates.Joint registry refreshed.erased.current emittedChild.occurrence r.id := by
  have branch : GeneralNominalJointCandidates.BranchAt registry refreshed.erased.current emittedChild.occurrence r.id witness :=
    ⟨r,by simp [registry],r_checked,rfl,rfl,preparedR,([(1,1)] : List (GeneralNominalInspection.Bounds refreshedSource)),locatedR,packetR_holds⟩
  refine ⟨?_,witness,witness_refreshed.1,branch,?_⟩
  · intro prior member same
    cases List.mem_singleton.mp member
    exact False.elim (child_identity_not_root (refreshed_alias_eq same))
  · intro site related
    have member := related.1
    rw [refreshed_sites] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact False.elim (child_identity_not_root (refreshed_alias_eq related.2))
    · exact branch

theorem enabledR : GeneralNominalFeedbackSteps.Installable registry refreshed.erased.current packetR := by
  refine ⟨⟨rfl,rfl,?_,by simp [registry],rfl,locatedR,preparedR,
    GeneralNominalFeedbackK2.selected_legacy selectedR,compatibleR,mergesClosedR,
    ⟨witness,witness_refreshed.1,packetR_holds⟩,jointR⟩,selectedR,feedbackMergesClosedR⟩
  rw [refreshed_sites]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

abbrev headSchemaR : GeneralNominalMaterialization.Schema where
  variables := [⟨0,.structural (.source 1) .pair 0,.actual⟩,⟨1,.structural (.source 1) .pair 1,.actual⟩]
  tests := [(.source 1,.structural .pair)]

theorem headSchemaR_exact : planR.headSchema = headSchemaR := by
  unfold Plan.headSchema
  change GeneralNominalMaterialization.schemas
    (GeneralNominalInspection.queries refreshedSource interpretation r) _ .actual 0 = _
  rw [queriesR]
  have roots : List.ofFn planR.input.center = [1] := by
    change (List.ofFn fun index : Fin 1 => _) = _
    simp only [List.ofFn_succ,List.ofFn_zero]
    exact congrArg (fun n => [n]) (childP_center childSignature ⟨0,by change 0 < 1; omega⟩)
  change GeneralNominalMaterialization.schemas
    [.node .pair [.variables [0],.variables [1]]]
    (fun index => .source ((List.ofFn planR.input.center)[index]?.getD 0)) .actual 0 = _
  rw [roots]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,headSchemaR]

theorem binderR_zero : planR.binder 0 = outputP := by
  have cap : (capture packetR).inputs 0 = (outputP,outputP) := by unfold capture; rw [bindingsR]; rfl
  simp only [Plan.binder,show (0 : Nat) ∉ packetR.declaration.outputNames by decide +kernel,ite_false,cap]
  rfl
theorem binderR_one : planR.binder 1 = outputP := by
  have cap : (capture packetR).inputs 1 = (outputP,outputP) := by unfold capture; rw [bindingsR]; rfl
  simp only [Plan.binder,show (1 : Nat) ∉ packetR.declaration.outputNames by decide +kernel,ite_false,cap]
  rfl
theorem headSchemaR_holds (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models refreshedSource model) : planR.SchemaHolds planR.headSchema model := by
  rw [headSchemaR_exact]
  constructor
  · intro test member; cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    refine ⟨[(model outputP).1,(model outputP).1],rfl,?_⟩
    exact GeneralNominalState.normalized_models refreshedSource model valid 1 (.pair (.var 4) (.var 4)) rfl
  · intro entry member
    simp only [headSchemaR,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · change GeneralNominalOriginTerms.Same model (.structural (.source 1) .pair 0) (.source (planR.binder 0))
      rw [binderR_zero]
      exact GeneralNominalStructuralReadback.actual_structural_readback
        (GeneralNominalSaturationState.initial refreshedContext emittedChild.occurrence) ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩
        (fun _ : Fin 2 => (4 : Fin 5)) rfl ⟨0,by decide +kernel⟩ model
        ((GeneralNominalSaturationState.initial_models ..).mpr valid)
    · change GeneralNominalOriginTerms.Same model (.structural (.source 1) .pair 1) (.source (planR.binder 1))
      rw [binderR_one]
      exact GeneralNominalStructuralReadback.actual_structural_readback
        (GeneralNominalSaturationState.initial refreshedContext emittedChild.occurrence) ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩
        (fun _ : Fin 2 => (4 : Fin 5)) rfl ⟨1,by decide +kernel⟩ model
        ((GeneralNominalSaturationState.initial_models ..).mpr valid)

theorem inputSchemaR_holds (model : GeneralNominalCommonBridge.Assignment) :
    planR.SchemaHolds (inputSchema packetR) model := by
  rw [inputSchemaR_exact]
  constructor <;> intro _ member <;> cases member

theorem childR_center (valid : childS.Signature roles) : ∀ index,
    (planR.childSite childS valid).center index = outputP := by
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  change planR.emittedCenter childS.id index.val (childS.arguments[index.val]'_) = outputP
  simp only [zero,childS,List.getElem_cons_zero,Plan.emittedCenter,normalize]
  exact binderR_zero

theorem childR_arguments (valid : childS.Signature roles) : ∀ index,
    (planR.childSite childS valid).occurrence.demand.arguments index = (outputP,outputP) := by
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  simp [Plan.childSite,GeneralNominalFeedbackSites.clauseChild,GeneralNominalFeedbackSites.frame,
    GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDictionaryEmissionPlans.occurrence,GeneralNominalAllocation.frame,childS,zero,normalize]
  change (capture packetR).inputs 0 = _
  unfold capture
  rw [bindingsR]
  rfl

theorem childR_schema (valid : childS.Signature roles) :
    planR.schema (planR.childRequests childS valid) =
      { variables := [⟨0,.source outputP,.actual⟩] } := by
  have requests : planR.childRequests childS valid = [⟨.var 0,outputP,.actual⟩] := by
    unfold Plan.childRequests
    change (List.ofFn fun index : Fin 1 => _) = _
    simp [List.ofFn_succ,childS]
    exact childR_center valid ⟨0,by change 0 < 1; omega⟩
  rw [requests]
  simp [Plan.schema,GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,
    normalize,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]

theorem childrenR_holds (model : GeneralNominalCommonBridge.Assignment) :
    ∀ clause ∈ packetR.declaration.requirements, ∀ valid : clause.Signature roles,
      (planR.childSite clause valid).Holds model ∧
        planR.SchemaHolds (planR.schema (planR.childRequests clause valid)) model := by
  intro clause member valid
  cases List.mem_singleton.mp member
  constructor
  · intro index
    unfold GeneralNominalCaptureMerges.Fits
    rw [childR_arguments,childR_center]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [childR_schema]
    constructor
    · intro test member; cases member
    · intro entry member; cases List.mem_singleton.mp member
      change GeneralNominalOriginTerms.Same model (.source outputP) (.source (planR.binder 0))
      rw [binderR_zero]
      exact GeneralNominalOriginTerms.source_self _ _

theorem binderR_fits (model : GeneralNominalCommonBridge.Assignment) :
    ∀ name, name ∈ packetR.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed packetR name →
      GeneralNominalCaptureMerges.Fits model ((capture packetR).inputs name) (model (planR.binder name)).1 := by
  intro name member
  have two : name = 0 ∨ name = 1 := by
    rcases member with direct|⟨clause,member,needed⟩
    · simpa [packetR,r,Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] using direct
    · cases List.mem_singleton.mp member
      simp [childS,normalizeArgs,normalize,variablesArgs,Pattern.variables] at needed
      exact Or.inl needed
  rcases two with rfl|rfl
  · rw [binderR_zero]
    change GeneralNominalCaptureMerges.Fits model (GeneralNominalAllocation.capture refreshedSource registry emittedChild.occurrence.identity r.id packetR.bindings |>.inputs 0) _
    rw [bindingsR]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [binderR_one]
    change GeneralNominalCaptureMerges.Fits model (GeneralNominalAllocation.capture refreshedSource registry emittedChild.occurrence.identity r.id packetR.bindings |>.inputs 1) _
    rw [bindingsR]
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem centered_inputsR (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models refreshedSource model) : GeneralNominalCenteredSupport.Inputs planR model := by
  refine ⟨inputsR model,?_,binderR_fits model,headSchemaR_holds model valid,inputSchemaR_holds model,childrenR_holds model⟩
  intro index
  unfold GeneralNominalCaptureMerges.Fits
  rw [childP_arguments,childP_center]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem namedSchemaR_holds (model : GeneralNominalCommonBridge.Assignment) :
    planR.SchemaHolds (namedSchema packetR) model := by
  rw [schemaR_exact]
  constructor
  · intro test member; cases member
  · intro entry member; cases List.mem_singleton.mp member
    change GeneralNominalOriginTerms.Same model (.source outputP) (.source (planR.binder 0))
    rw [binderR_zero]
    exact GeneralNominalOriginTerms.source_self _ _

theorem planR_holds : planR.Holds witness := by
  have inputs := centered_inputsR witness witness_refreshed.1.1
  exact ⟨packetR_holds,inputs.2.1,inputs.2.2.1,inputs.2.2.2.1,inputs.2.2.2.2.1,
    namedSchemaR_holds witness,inputs.2.2.2.2.2⟩

theorem graph_tests_refreshed : (graph refreshed).tests = [(.source 0,.structural .pair)] := by
  change GeneralNominalCenteredSteps.Plan.tests planP ++ [] = _
  simp only [List.append_nil]
  unfold GeneralNominalCenteredSteps.Plan.tests
  rw [headSchemaP_exact,schemaP_exact]
  change [(.source 0,.structural .pair)] ++
    ([childR].attach.flatMap fun clause =>
      (planP.schema (planP.childRequests clause.val (p_checked.signature.2.2.2 clause.val clause.property))).tests) = _
  simp only [List.attach_cons,List.attach_nil,List.flatMap_cons,List.flatMap_nil]
  rw [childP_schema]
  rfl

theorem pair_child_not_root (index : Fin 2) :
    ¬ GeneralNominalOriginTerms.Same witness (.structural (.source 0) .pair index.val) (.source 0) := by
  have readback := GeneralNominalStructuralReadback.actual_structural_readback
    (GeneralNominalSaturationState.initial context root) ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩
    (fun i : Fin 2 => if i.val = 0 then (1 : Fin 4) else (2 : Fin 4)) rfl index witness
    ((GeneralNominalSaturationState.initial_models ..).mpr witness_source)
  intro same
  have equal := GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm readback) same
  by_cases zero : index.val = 0
  · simp only [zero,ite_true] at equal
    have models := equal.2.2 _ _ (.source _) (.source _)
    have mass := GeneralNominalBranchingMass.equivalent_mass (witnessTree 1) (witnessTree 0) models
    change 3 = 5 at mass
    omega
  · simp only [zero,ite_false] at equal
    have models := equal.2.2 _ _ (.source _) (.source _)
    have mass := GeneralNominalBranchingMass.equivalent_mass (witnessTree 2) (witnessTree 0) models
    change 1 = 5 at mass
    omega

theorem graph_acyclic_refreshed (origin : Origin) : ¬ GeneralNominalCenteredGraph.Cyclic (graph refreshed) origin := by
  have property : ∀ first last, GeneralNominalCenteredGraph.Edge (graph refreshed) first last →
      GeneralNominalOriginTerms.Same witness first (.source 0) ∧
      ¬ GeneralNominalOriginTerms.Same witness last (.source 0) := by
    rintro first last ⟨parent,child,recorded,one,two⟩
    cases recorded with
    | structural shape index member =>
      rw [graph_tests_refreshed] at member
      have exactTest := List.mem_singleton.mp member
      cases exactTest
      exact ⟨one witness witness_refreshed,fun same => pair_child_not_root index
        (GeneralNominalOriginTerms.same_trans (two witness witness_refreshed) same)⟩
    | nominal name arity index member =>
      rw [graph_tests_refreshed] at member
      have impossible := List.mem_singleton.mp member
      cases impossible
  rintro ⟨⟨next,edge,path⟩,_⟩
  have one := property _ _ edge
  cases path with
  | nil => exact one.2 one.1
  | cons edge _ => exact one.2 (property _ _ edge).1

theorem refreshed_no_cyclic (origin : Origin) : ¬ Cyclic refreshed origin := by
  rintro (⟨identity,_,cycle,_⟩|cycle)
  · exact refreshed_no_feedback identity cycle
  · exact graph_acyclic_refreshed origin cycle

theorem source_guardR : GeneralNominalSupportChoices.PacketGuard refreshed.erased packetR [] := by
  have reads : ∀ slot ∈ GeneralNominalSupport.readsMany refreshedSource
      (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)],
      GeneralNominalSupport.ReadyAt refreshed.erased [] (refreshedIdentifiers slot) := by
    intro slot member
    rw [readsR] at member
    have zero : slot = (1 : Fin 5) := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
    subst slot
    exact readyR
  have roots : GeneralNominalSupport.Roots refreshed.erased [] emittedChild.occurrence := by
    intro index
    rw [childP_arguments childSignature index]
    exact readyR
  refine ⟨⟨(by intro _ member; cases member),roots,reads⟩,
    ⟨(by intro _ member; cases member),roots,?_⟩⟩
  intro declaration visible role bounds located
  have same := r_only declaration visible role
  subst declaration
  have exactBounds := Option.some.inj (located.symm.trans locatedR)
  subst bounds
  exact reads

theorem centered_decisionR : DecisionGuard registry refreshed emittedChild.occurrence := by
  apply GeneralNominalCenteredSupport.legacy_decision
  have ready : GeneralNominalSharedSupport.ReadyAt refreshed.erased 1 :=
    ⟨.structural .pair,_,current_headR,GeneralNominalSharedSupport.source_head refreshed.erased old_headR⟩
  refine ⟨?_,?_⟩
  · intro index
    rw [childP_arguments childSignature index]
    exact ready
  intro declaration visible role bounds located slot member
  have same := r_only declaration visible role
  subst declaration
  have exactBounds := Option.some.inj (located.symm.trans locatedR)
  subst bounds
  change slot ∈ GeneralNominalSupport.readsMany refreshedSource (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)] at member
  rw [readsR] at member
  have zero : slot = (1 : Fin 5) := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  subst slot
  exact ready

theorem inspectionR_count (candidate : Plan roles)
    (same : candidate.input = planR.input) (ctx : candidate.packet.context = refreshedContext)
    (decl : candidate.packet.declaration = r)
    (located : arguments candidate.packet.context candidate.input.occurrence = some candidate.packet.bounds) :
    (inspection candidate).inspected.length = (inspection candidate).tests.length := by
  rcases candidate with ⟨⟨reg,ctxt,site,declaration,certified,bounds⟩,input,exactInput⟩
  change input = planR.input at same
  subst input
  change ctxt = refreshedContext at ctx
  subst ctxt
  change declaration = r at decl
  subst declaration
  change arguments refreshedContext emittedChild.occurrence = some bounds at located
  have exactBounds := Option.some.inj (located.symm.trans locatedR)
  subst bounds
  unfold inspection
  change (inspectMany refreshedSource (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)]
    (fun index => ((planR.input.observed.inputs[index]?).join)) 0).inspected.length =
      (inspectMany refreshedSource (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)]
    (fun index => ((planR.input.observed.inputs[index]?).join)) 0).tests.length
  rw [queriesR]
  have atOne : refreshedSource.view.heads 1 = .structural 0 (fun _ => 4) := rfl
  have observed : planR.input.observed.inputs[0]?.join = some (.source 1) := by
    change ((List.ofFn fun index : Fin 1 => some (Origin.source (emittedChild.center index)))[0]?).join = _
    simp only [List.ofFn_succ,List.ofFn_zero,List.getElem?_cons_zero,Option.join_some]
    exact congrArg (fun n => some (Origin.source n))
      (childP_center childSignature ⟨0,by change 0 < 1; omega⟩)
  simp only [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_4,atOne,observed]
  change ((Report.visit (1,1) (some (.source 1)) (.structural .pair)
    (inspectMany refreshedSource [.variables [0],.variables [1]] [(4,4),(4,4)]
      (fun index => some (.structural (.source 1) .pair index)) 0)).append {}).inspected.length =
    ((Report.visit (1,1) (some (.source 1)) (.structural .pair)
    (inspectMany refreshedSource [.variables [0],.variables [1]] [(4,4),(4,4)]
      (fun index => some (.structural (.source 1) .pair index)) 0)).append {}).tests.length
  simp [inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,Report.visit,Report.append]

theorem safeR : Safe refreshed planR :=
  ⟨inspectionR_count planR rfl rfl rfl locatedR,fun entry _ => refreshed_no_cyclic entry.1⟩

theorem alternativesR : AlternativesSafe registry refreshed planR.input := by
  intro candidate same registrySame contextSame visible role headReady located
  have exactRole : candidate.packet.declaration.role = emittedChild.occurrence.demand.role := role
  have declarationSame := r_only candidate.packet.declaration visible exactRole
  have argumentsSame : arguments candidate.packet.context candidate.input.occurrence = some candidate.packet.bounds := by
    rw [same]
    exact located
  exact ⟨inspectionR_count candidate same contextSame declarationSame argumentsSame,
    fun entry _ => refreshed_no_cyclic entry.1⟩

theorem centered_child_registered : planR.input ∈ refreshed.sites := by
  change emittedChild ∈ [planP.input] ++ planP.emitted
  exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨childR,List.mem_singleton_self _⟩,by simp,rfl⟩)

theorem guardR : PacketGuard refreshed planR [] := by
  refine ⟨centered_child_registered,GeneralNominalValueSupport.source_packet _ _ source_guardR,
    centered_decisionR,safeR,alternativesR,?_,witness,witness_refreshed,planR_holds⟩
  constructor
  · rintro ⟨site,member,same,index,cyclic⟩
    exact refreshed_no_cyclic _ cyclic
  · rintro ⟨plan,member,same,reg,ctx,visible,role,headReady,located,entry,present,cyclic⟩
    exact refreshed_no_cyclic _ cyclic

abbrev childSSignature : childS.Signature roles := r_checked.signature.2.2.2 childS (List.mem_singleton_self _)
noncomputable abbrev emittedS : Site roles := planR.childSite childS childSSignature

theorem novelR : ¬ GeneralNominalFeedbackSteps.Committed refreshed.erased.current packetR := by
  intro committed
  have member : emittedS.occurrence ∈ packetR.children :=
    GeneralNominalCenteredProgress.clause_child_member planR childS (List.mem_singleton_self _) childSSignature
  have edge := committed.2 emittedS.occurrence member
  change (emittedChild.occurrence,emittedS.occurrence) ∈ [] ++
    packetP.children.map (fun child => (root,child)) at edge
  rw [childrenP_exact] at edge
  have same := List.mem_singleton.mp edge
  exact child_identity_not_root (congrArg (fun edge => edge.1.identity) same)

theorem generatedR : GeneralNominalSaturationState.Generated refreshed.erased.current root emittedChild.occurrence := by
  refine .child .root ?_
  change (root,emittedChild.occurrence) ∈ [] ++ packetP.children.map (fun child => (root,child))
  rw [childrenP_exact]
  exact List.mem_singleton_self _

theorem stepR : Step registry root refreshed afterR :=
  ⟨emittedChild.occurrence,generatedR,.install planR [] enabledR novelR guardR⟩

end Yulang.GeneralNominalCenteredSourceRefreshWitness
