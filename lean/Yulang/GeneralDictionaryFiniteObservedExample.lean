import Yulang.GeneralDictionaryObservedFiniteRequests
import Yulang.GeneralNominalExamples
import Yulang.GeneralNominalSourceFormation
import Yulang.GeneralDictionaryObservedScalarRequests
import Yulang.GeneralDictionaryScalarLeaf

/-! A genuinely ternary nominal request, with an inhabited source model and
four exact materialization tests and an actual named-output semantic dictionary.
Initial reachability is proved; stable execution is not asserted. -/
namespace Yulang.GeneralDictionaryFiniteObservedExample
open GeneralDictionaryObservedFiniteRequests GeneralNominalMaterialization

abbrev descriptor : GeneralNominalState.Descriptor 2 :=
  ⟨0, ⟨[.type,.type,.type],0⟩, [.type (1,1),.type (1,1),.type (1,1)], rfl⟩

abbrev constructors : GeneralDeclarationPatterns.Constructors :=
  fun name => if name = 0 then some descriptor.declaration else if name = 2 then some ⟨[],0⟩ else none

abbrev state : GeneralNominalState.State where
  seed := 1
  base := GeneralNominalExamples.base true
  view := GeneralNominalExamples.view true
  constructors := constructors
  nominals := fun slot => if slot = 0 then some descriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · have same := Option.some.inj recorded
      subst d
      rfl
    · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases zero : slot = 0
    · subst slot; rfl
    · simp [zero] at recorded

abbrev interpretation := GeneralNominalExamples.interpretation
abbrev arguments : List CommonNominalFullCarrier.Argument :=
  [.inl (.base .int),.inl (.base .int),.inl (.base .int)]
abbrev model : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source = 0 then CommonNominalFullCarrier.nominal 0 arguments else .base .int, Common.rowEmpty)

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, by simp [PresenceNormalForm.All]⟩
  · intro atom member
    change atom ∈ GeneralSourceState.equationAtoms (1 : Fin 2) (.base .int) at member
    simp only [GeneralSourceState.equationAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot term recorded
    by_cases yes : slot = 1
    · subst slot
      have equal : (.base .int : Core.PresenceGeneration.TyTerm (Fin 2)) = term := by
        simpa [GeneralNominalExamples.heads, GeneralSourceState.Head.equation] using recorded
      subst term
      exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
    · simp [GeneralNominalExamples.heads, yes, GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [GeneralNominalExamples.base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot
      have same : descriptor = d := Option.some.inj recorded
      subst d
      refine ⟨arguments, ?_, ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩⟩
      exact .cons ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
        (.cons ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
          (.cons ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩ .nil))
    · simp [state, zero] at recorded

abbrev query : GeneralNominalInspection.Query := .nominal 0 [.scalar .int,.scalar .int,.scalar .int]
abbrev request : Request := ⟨.app 0 [.app 2 [],.app 2 [],.app 2 []],0,.actual⟩

abbrev tree : Tree state 0 query := by
  have h := Tree.nominal (state := state) 0 descriptor rfl (n := 3)
    (fun _ => 1) (fun _ => GeneralNominalInspection.Query.scalar .int)
    (by simp [List.ofFn_succ]) (fun _ => Tree.scalar 1 .int rfl)
  simpa [query,List.ofFn_succ] using h

theorem translation : GeneralNominalInspection.translate state.constructors interpretation
    (GeneralDeclarationPatterns.normalize request.pattern) = query := by
  simp [GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.normalizeArgs,interpretation,GeneralNominalExamples.interpretation,
    constructors,query]

theorem observed : Observed state interpretation [request] := by
  intro r member
  have same := List.mem_singleton.mp member
  subst r
  refine ⟨0,rfl,?_⟩
  rw [translation]
  exact ⟨tree⟩

/-- Arity three is not represented by any constructor of the old binary tree. -/
theorem no_closed_tree (slot : Fin state.base.slots) :
    ¬ Nonempty (GeneralDictionaryObservedClosedRequests.Tree state slot query) := by
  intro ⟨h⟩
  have bound : ∀ {q}, GeneralDictionaryObservedClosedRequests.Tree state slot q →
      ∀ name args, q = .nominal name args → args.length ≤ 2 := by
    intro q witness name args equal
    cases witness <;> cases equal <;> simp
  have impossible := bound h 0 _ rfl
  simp at impossible

theorem not_closed_observed :
    ¬ GeneralDictionaryObservedClosedRequests.Observed state interpretation [request] := by
  intro observed
  obtain ⟨slot,_,witness⟩ := observed request (List.mem_singleton_self _)
  rw [translation] at witness
  exact no_closed_tree slot witness

/-- Actual materialization retains the nominal test and all three distinct
projection paths, even though the scalar source slot is shared. -/
theorem tests_exact : (generated state interpretation [request]).tests =
    [(.source 0,.nominal 0 3),
     (.nominal (.source 0) 0 0,.scalar .int),
     (.nominal (.source 0) 0 1,.scalar .int),
     (.nominal (.source 0) 0 2,.scalar .int)] := by
  simp [generated,request,GeneralNominalInspection.translate,
    GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
    interpretation,GeneralNominalExamples.interpretation,constructors,
    schema,schemas,Schema.append]

theorem every_source_model (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : GeneralNominalRecursiveInspection.Report state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Models state declaration capture report (generated state interpretation [request]) assignment :=
  generated_models state interpretation [request] observed declaration capture report assignment valid

theorem inhabited_request_models (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : GeneralNominalRecursiveInspection.Report state) :
    GeneralNominalState.Models state model ∧
      Models state declaration capture report (generated state interpretation [request]) model :=
  ⟨state_models,every_source_model declaration capture report model state_models⟩

open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles)

abbrev equation : Equation := ⟨0,0,request.pattern⟩
abbrev declaration : Declaration := ⟨154,1,[.app 2 []],[],[equation],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev demand : GeneralSourceState.Demand roles := ⟨1,fun _ => (1,1),[⟨0,0⟩],by
  intro o member
  have same := List.mem_singleton.mp member
  subst o
  exact ⟨none,rfl⟩⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨154,demand⟩

/-- A closed scalar input produces a ternary nominal named output. -/
theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro e member
      have same := List.mem_singleton.mp member; subst e
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨equation,by simp,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at present
    · intro c member; cases member
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c member; cases member
  · intro c member; cases member
  · intro c member; cases member
  · intro c member; cases member

theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro d member
  have same := List.mem_singleton.mp member
  subst d
  exact checked

theorem named_request_present : root.demand.outputs ≠ [] := by intro h; cases h

theorem actual_requests_exact (captures : GeneralNominalAllocation.Bindings) :
    requests state registry root declaration checked captures = [request] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by
    intro clause member; cases member)]
  rfl

/-- The observed ternary certificate discharges actual named-output constraints,
not only a manually supplied materialization request. -/
theorem actual_request_models (captures : GeneralNominalAllocation.Bindings)
    (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Models state declaration capture report
      (generated state interpretation (requests state registry root declaration checked captures)) assignment := by
  rw [actual_requests_exact]
  exact every_source_model declaration capture report assignment valid

open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence
abbrev context : Context := ⟨state,interpretation⟩

theorem metadata : Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name base found
  change (if name = 2 then some (GeneralCandidateInspection.Primitive.scalar .int) else none) = some base at found
  split at found
  · subst name; cases found; exact ⟨_,rfl,rfl⟩
  · cases found

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      simp [GeneralNominalState.sources,List.ofFn_succ]
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := by
    intro id member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> subst id <;> decide +kernel
  unallocated := rfl

theorem report_exact : report context declaration [(1,1)] =
    { inspected := [(1,1)], checked := [(1,1),(1,1)] } := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,
    normalizeArgs,normalize,GeneralNominalInspection.translate,interpretation,
    GeneralNominalExamples.interpretation,inspectMany,inspect,
    Report.visit,Report.append]

theorem branch_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    BranchModels registry context root declaration checked [(1,1)] assignment := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact CommonNominalFullCarrier.subtype_refl _
  · rw [report_exact]
    simp [ProjectionModels]
  · exact actual_request_models _ _ _ assignment valid

theorem ready : RequestReady registry context root declaration checked [(1,1)] := by
  constructor
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨equation,List.mem_singleton_self _,rfl⟩
  · unfold GeneralNominalRecursiveCandidates.generated
    rw [actual_requests_exact]
    exact (generated_shape state interpretation [request] observed).2

theorem actual_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Instance registry context assignment root declaration.id [] := by
  refine ⟨declaration,by simp,checked,rfl,rfl,[(1,1)],?_,?_,ready,?_,metadata,branch_models assignment valid⟩
  · decide +kernel
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked rfl _).symm

theorem full_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Evidence registry context assignment root (.node declaration.id []) :=
  (evidence_leaf_iff registry context assignment root declaration.id).mpr (actual_instance assignment valid)

abbrev start := GeneralNominalSupport.initial context root

theorem actual_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,initial_source,rfl⟩,.refl⟩

/-- Initial reachability and semantic evidence coexist with a genuine ternary
named output. This statement does not claim final stability or execution. -/
theorem reachable_inhabited_named_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    Evidence registry context model root (.node declaration.id []) ∧ root.demand.outputs ≠ [] :=
  ⟨actual_reachable,(GeneralNominalSaturationState.initial_models context root model).mpr state_models,
    full_evidence model state_models,named_request_present⟩

end Yulang.GeneralDictionaryFiniteObservedExample
