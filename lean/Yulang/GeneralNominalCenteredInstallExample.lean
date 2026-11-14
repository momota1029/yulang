import Yulang.GeneralNominalCenteredSteps
import Yulang.GeneralNominalGroundExamples
import Yulang.GeneralNominalBranchingMass
import Yulang.GeneralNominalCenteredInitialInventories
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
/-! A checked source with an unknown child and an actual guarded centered installation.
The finite witness establishes every installation guard without a transition premise. -/
namespace Yulang.GeneralNominalCenteredInstallExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms equationAtoms_exact)

abbrev roles : Roles.RoleDecls := fun role =>
  if role = 0 ∨ role = 1 then GeneralNominalProvenanceDeclarations.outputRole 1 0
  else GeneralNominalProvenanceDeclarations.bareRole 1
abbrev constructors := GeneralDeclarationExamples.constructors
abbrev childR : Clause := ⟨10,1,[.var 1],[⟨100,0,.var 2⟩]⟩
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
    (planP.childSite childR valid).center index = 2 := by
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  change planP.emittedCenter childR.id index.val (childR.arguments[index.val]'_) = 2
  simp only [zero,childR,List.getElem_cons_zero,Plan.emittedCenter,normalize]
  exact binderP_one

theorem childP_arguments (valid : childR.Signature roles) : ∀ index,
    (planP.childSite childR valid).occurrence.demand.arguments index = (2,2) := by
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  simp [Plan.childSite,GeneralNominalFeedbackSites.clauseChild,GeneralNominalFeedbackSites.frame,
    GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDictionaryEmissionPlans.occurrence,GeneralNominalAllocation.frame,childR,zero,normalize]
  change (capture packetP).inputs 1 = _
  unfold capture
  rw [bindingsP]
  rfl

theorem childP_schema (valid : childR.Signature roles) :
    planP.schema (planP.childRequests childR valid) =
      { variables := [⟨1,.source 2,.actual⟩] } := by
  have requests : planP.childRequests childR valid = [⟨.var 1,2,.actual⟩] := by
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
      change GeneralNominalOriginTerms.Same model (.source 2) (.source (planP.binder 1))
      rw [binderP_one]
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
      exact Or.inr needed
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

end Yulang.GeneralNominalCenteredInstallExample
