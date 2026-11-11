import Yulang.GeneralNominalCandidates
import Yulang.GeneralDeclarationExamples
import Yulang.GeneralCandidateConflictExamples

/-! Section 6.3 nominal examples use the dedicated full nominal constructor.
The list head has resolved name 0 and one invariant type interval. Its body
is absent. Display int remains a separate visible declaration. -/
namespace Yulang.GeneralNominalExamples

open GeneralDeclarationExamples (roles constructors display wrap display_checked wrap_checked)
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms equationAtoms_exact)
open GeneralDeclarations GeneralDeclarationPatterns

abbrev heads (known : Bool) : Fin 2 → GeneralSourceState.Head
    (fun i : Fin 0 => Fin.elim0 i : Fin 0 → GeneralSourceState.Shape 2) :=
  fun slot => if slot = 1 ∧ known = true then .scalar .int else .unresolved

abbrev base (known : Bool) : GeneralSourceState.State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := if known then equationAtoms 1 (.base .int) else []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := heads known
  intervals := [(0,0),(1,1)]
  heads_sound := by
    intro assignment valid slot term recorded
    by_cases yes : slot = 1 ∧ known = true
    · obtain ⟨rfl,rfl⟩ := yes
      have equal : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [heads, GeneralSourceState.Head.equation] using recorded
      subst term
      exact (equationAtoms_exact ..).mp valid
    · simp [heads, yes, GeneralSourceState.Head.equation] at recorded
  intervals_sound := by
    intro assignment _ pair member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _

abbrev view (known : Bool) : GeneralNormalizedObservation.Snapshot (base known) where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 1 ∧ known = true then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases yes : slot = 1 ∧ known = true
    · obtain ⟨rfl,rfl⟩ := yes
      have equal : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .head rfl
    · simp [yes, GeneralNormalizedObservation.Head.term, GeneralNormalizedObservation.Deferred.term] at recorded

abbrev listDescriptor : GeneralNominalState.Descriptor 2 :=
  ⟨0, ⟨[.type],0⟩, [.type (1,1)], rfl⟩

abbrev state (known : Bool) : GeneralNominalState.State where
  base := base known
  view := view known
  constructors := constructors
  nominals := fun slot => if slot = 0 then some listDescriptor else none
  catalogue := by
    intro slot descriptor recorded
    split at recorded
    · have same := Option.some.inj recorded
      subst descriptor
      rfl
    · cases recorded
  bodies_opaque := by
    intro slot descriptor recorded
    by_cases zero : slot = 0
    · subst slot; rfl
    · simp [zero] at recorded

abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun name => if name = 2 then some (.scalar .int) else none
  invariantNominal := fun name => name == 0
  disjoint := by intro name yes; simp_all

abbrev context (known : Bool) : GeneralNominalCandidates.Context := ⟨state known, interpretation⟩

abbrev intDisplay : Declaration := ⟨3,0,[.app 2 []],[],[],[]⟩

theorem int_display_checked : DeclarationChecked constructors roles intDisplay := by
  constructor
  · simp [Declaration.Signature, roles, GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize,
      variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  · simp
  · simp
  · simp
  · simp

abbrev registry : Registry := ⟨constructors, roles, [intDisplay,display,wrap]⟩

theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel, ?_⟩
  intro declaration member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact int_display_checked
  · exact display_checked
  · exact wrap_checked

abbrev displayDemand : GeneralSourceState.Demand roles :=
  ⟨0, fun _ => (0,0), [], by intro _ member; cases member⟩
abbrev wrapDemand : GeneralSourceState.Demand roles :=
  ⟨1, fun _ => (0,0), [], by intro _ member; cases member⟩
abbrev displayRoot : GeneralSourceDictionaries.Occurrence roles := ⟨100,displayDemand⟩
abbrev wrapRoot : GeneralSourceDictionaries.Occurrence roles := ⟨101,wrapDemand⟩
abbrev captured : GeneralNominalAllocation.Bindings := [(0,(1,1))]

abbrev model : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source = 0 then CommonNominalFullCarrier.nominal 0 [.inl (.base .int)] else .base .int, Common.rowEmpty)

theorem state_models (known : Bool) : GeneralNominalState.Models (state known) model := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, by simp [PresenceNormalForm.All]⟩
  · cases known with
    | false => exact PresenceNormalForm.all_nil _ _
    | true =>
        intro atom member
        change atom ∈ equationAtoms (1 : Fin 2) (.base .int) at member
        simp only [equationAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot term recorded
    by_cases yes : slot = 1 ∧ known = true
    · obtain ⟨rfl,rfl⟩ := yes
      have equal : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [heads, GeneralSourceState.Head.equation] using recorded
      subst term
      exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
    · simp [heads, yes, GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot descriptor recorded
    by_cases zero : slot = 0
    · subst slot
      have same : listDescriptor = descriptor := Option.some.inj recorded
      subst descriptor
      exact ⟨[.inl (.base .int)], .cons ⟨CommonNominalFullCarrier.subtype_refl _,
        CommonNominalFullCarrier.subtype_refl _⟩ .nil,
        ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩⟩
    · simp [state, zero] at recorded

theorem display_report (known : Bool) :
    GeneralNominalCandidates.report (context known) display [(0,0)] =
      { captures := [(0,(1,1))], inspected := [(0,0),(0,0)] } := by
  simp [GeneralNominalCandidates.report, GeneralNominalInspection.queries, Declaration.normalHead,
    normalizeArgs, normalize, GeneralNominalInspection.translate, interpretation,
    GeneralNominalInspection.inspectMany, GeneralNominalInspection.inspect,
    GeneralNominalInspection.typeArguments, GeneralNominalInspection.Report.append,
    GeneralNominalInspection.Report.visit]
  repeat first
    | rw [GeneralNominalInspection.inspectMany.eq_2]
    | rw [GeneralNominalInspection.inspectMany.eq_1]
    | rw [GeneralNominalInspection.inspect.eq_1]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem wrap_report (known : Bool) :
    GeneralNominalCandidates.report (context known) wrap [(0,0)] =
      { captures := [(0,(1,1))], inspected := [(0,0),(0,0)] } := by
  simp [GeneralNominalCandidates.report, GeneralNominalInspection.queries, Declaration.normalHead,
    normalizeArgs, normalize, GeneralNominalInspection.translate, interpretation,
    GeneralNominalInspection.inspectMany, GeneralNominalInspection.inspect,
    GeneralNominalInspection.typeArguments, GeneralNominalInspection.Report.append,
    GeneralNominalInspection.Report.visit]
  repeat first
    | rw [GeneralNominalInspection.inspectMany.eq_2]
    | rw [GeneralNominalInspection.inspectMany.eq_1]
    | rw [GeneralNominalInspection.inspect.eq_1]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem int_report (known : Bool) :
    GeneralNominalCandidates.report (context known) intDisplay [(0,0)] =
      { inspected := [(0,0),(0,0)], conflicts := [(0,0)] } := by
  simp [GeneralNominalCandidates.report, GeneralNominalInspection.queries, Declaration.normalHead,
    normalizeArgs, normalize, GeneralNominalInspection.translate, interpretation,
    GeneralNominalInspection.inspectMany, GeneralNominalInspection.inspect,
    GeneralNominalInspection.Report.append,
    GeneralNominalInspection.Report.visit]

abbrev displayChild : GeneralSourceDictionaries.Occurrence roles :=
  ⟨GeneralNominalAllocation.source (state true) registry 100
      (GeneralNominalAllocation.origin 100 1 6 10 0),
    ⟨0,fun _ => (1,1),[], by intro _ member; cases member⟩⟩

abbrev itemTarget : Nat := GeneralNominalAllocation.source (state true) registry 101
  (GeneralNominalAllocation.origin 101 2 2 1 0)

abbrev wrapChild : GeneralSourceDictionaries.Occurrence roles :=
  ⟨GeneralNominalAllocation.source (state true) registry 101
      (GeneralNominalAllocation.origin 101 2 6 20 0),
    ⟨2,fun _ => (1,1),[⟨1,itemTarget⟩], by
      intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨none,rfl⟩⟩⟩

theorem display_children :
    GeneralNominalAllocation.children (state true) registry displayRoot display display_checked captured = [displayChild] := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration, GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll, GeneralDeclarationDemands.emit,
    GeneralDictionaryEmissionPlans.occurrence, GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval, GeneralNominalAllocation.frame,
    GeneralNominalAllocation.capture, GeneralNominalAllocation.occurrences, captured, normalize, displayChild]

theorem wrap_children :
    GeneralNominalAllocation.children (state true) registry wrapRoot wrap wrap_checked captured = [wrapChild] := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration, GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll, GeneralDeclarationDemands.emit,
    GeneralDictionaryEmissionPlans.occurrence, GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval, GeneralDeclarationDemands.outputTarget,
    Declaration.outputNames, GeneralNominalAllocation.frame, GeneralNominalAllocation.capture,
    GeneralNominalAllocation.occurrences, captured, normalize, wrapChild, itemTarget]

theorem wrap_item_equation : wrapChild.demand.outputs = [⟨1,itemTarget⟩] := rfl

theorem item_target_fresh : itemTarget ∉ GeneralNominalState.sources (state true) := by
  intro member
  apply GeneralNominalAllocation.source_initial_fresh (state true) registry 101
    (GeneralNominalAllocation.origin 101 2 2 1 0) itemTarget _ rfl
  have bound : (GeneralNominalState.sources (state true)).foldr max 0 = (state true).seed := rfl
  rw [← bound]
  exact GeneralNominalAllocation.member_le_max _ _ member

private theorem metadata : GeneralNominalCandidates.Metadata registry (context true) := by
  refine ⟨rfl, ?_⟩
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
    subst primitive
    exact ⟨⟨[],2⟩,rfl,rfl⟩
  · simp [two] at recorded

private theorem fresh (root : Nat) : GeneralNominalAllocation.Fresh (state true) registry root := by
  intro key _ collision
  have bound : (GeneralNominalState.sources (state true)).foldr max 0 = (state true).seed := rfl
  have below := GeneralNominalAllocation.member_le_max _ _ collision
  rw [bound] at below
  exact False.elim (GeneralNominalAllocation.source_initial_fresh (state true) registry root key _ below rfl)

private theorem captured_models (root : Nat) (declaration : Declaration)
    (names : declaration.inputNames = [0]) :
    GeneralNominalState.Models
      (GeneralNominalAllocation.propagate (state true) registry root declaration captured) model := by
  apply (GeneralNominalAllocation.propagate_models ..).mpr
  refine ⟨state_models true, ?_, ?_⟩
  · intro first one last two _
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact CommonNominalFullCarrier.subtype_refl _
  · simp [GeneralNominalAllocation.merges, names, GeneralNominalAllocation.occurrences, captured]

private theorem covered : GeneralNominalInspection.Covered (state true)
    { captures := [(0,(1,1))], inspected := [(0,0),(0,0)] } := by
  intro bounds member
  have same : bounds = (0,0) := by simpa using member
  subst bounds
  exact Or.inl ⟨listDescriptor,rfl,by unfold GeneralNominalInspection.NominalSupported; decide +kernel⟩

private theorem display_located : GeneralNominalCandidates.arguments (context true) displayRoot = some [(0,0)] := by
  decide +kernel

private theorem wrap_located : GeneralNominalCandidates.arguments (context true) wrapRoot = some [(0,0)] := by
  decide +kernel

private theorem display_linked : GeneralNominalState.Linked (state true) displayDemand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources, List.ofFn_succ]
  · intro output member; cases member

private theorem wrap_linked : GeneralNominalState.Linked (state true) wrapDemand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources, List.ofFn_succ]
  · intro output member; cases member

private theorem display_ready : ¬ GeneralNominalState.RootPending (state true) displayDemand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨listDescriptor,rfl⟩⟩

private theorem wrap_ready : ¬ GeneralNominalState.RootPending (state true) wrapDemand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨listDescriptor,rfl⟩⟩

private theorem display_emissions :
    GeneralNominalCandidates.EmissionsReady registry (context true) displayRoot display display_checked [(0,0)] := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [GeneralCanonicalChildOrder.canonicalEmit, GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements, GeneralDeclarationDemands.emitAll,
      GeneralDeclarationDemands.emit, GeneralDeclarationDemands.childDemand, GeneralDeclarationDemands.inputInterval,
      GeneralNominalAllocation.capture, GeneralNominalAllocation.occurrences,
      GeneralNominalInspection.bindings, normalize, List.ofFn_succ]
    rw [display_report]
    simp
  · change ∀ child ∈ GeneralNominalAllocation.children (state true) registry displayRoot display display_checked
        (GeneralNominalInspection.bindings (state true) (GeneralNominalCandidates.report (context true) display [(0,0)])), _
    rw [display_report]
    change ∀ child ∈ GeneralNominalAllocation.children (state true) registry displayRoot display display_checked captured, _
    rw [display_children]
    intro child member
    have same := List.mem_singleton.mp member
    subst child
    constructor
    · intro index
      constructor <;> simp [GeneralNominalState.sources, GeneralNominalCandidates.privateState,
        GeneralNominalAllocation.propagate, GeneralNominalState.extend, List.ofFn_succ]
    · intro output member; cases member

private theorem wrap_emissions :
    GeneralNominalCandidates.EmissionsReady registry (context true) wrapRoot wrap wrap_checked [(0,0)] := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [GeneralCanonicalChildOrder.canonicalEmit, GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements, GeneralDeclarationDemands.emitAll,
      GeneralDeclarationDemands.emit, GeneralDeclarationDemands.childDemand, GeneralDeclarationDemands.inputInterval,
      GeneralDeclarationDemands.outputTarget, Declaration.outputNames,
      GeneralNominalAllocation.capture, GeneralNominalAllocation.occurrences,
      GeneralNominalInspection.bindings, normalize, List.ofFn_succ]
    rw [wrap_report]
    simp
  · change ∀ child ∈ GeneralNominalAllocation.children (state true) registry wrapRoot wrap wrap_checked
        (GeneralNominalInspection.bindings (state true) (GeneralNominalCandidates.report (context true) wrap [(0,0)])), _
    rw [wrap_report]
    change ∀ child ∈ GeneralNominalAllocation.children (state true) registry wrapRoot wrap wrap_checked captured, _
    rw [wrap_children]
    intro child member
    have same := List.mem_singleton.mp member
    subst child
    constructor
    · intro index
      constructor <;> simp [GeneralNominalState.sources, GeneralNominalCandidates.privateState,
        GeneralNominalAllocation.propagate, GeneralNominalState.extend, List.ofFn_succ]
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      simp [GeneralNominalState.sources, GeneralNominalCandidates.privateState,
        GeneralNominalAllocation.propagate, GeneralNominalState.extend,
        GeneralNominalAllocation.reserved, GeneralNominalAllocation.keys,
        GeneralNominalAllocation.declarationKeys, itemTarget, List.ofFn_succ,
        Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize,
        variablesArgs, Pattern.variables]

theorem display_survivor :
    GeneralNominalCandidates.Survivor registry (context true) displayRoot 1 [displayChild] := by
  refine ⟨display_ready, display, by simp, display_checked, rfl, rfl, [(0,0)], display_located, ?_, ?_⟩
  · refine ⟨metadata, display_linked, fresh 100, [(0,0)], display_located, ?_, ?_, ?_, display_emissions⟩
    · rw [display_report]; exact ⟨rfl,rfl,rfl⟩
    · rw [display_report]; exact covered
    · refine ⟨model, ?_⟩
      unfold GeneralNominalCandidates.privateState
      rw [display_report]
      exact captured_models 100 display rfl
  · rw [display_report]
    exact display_children.symm

theorem wrap_survivor :
    GeneralNominalCandidates.Survivor registry (context true) wrapRoot 2 [wrapChild] := by
  refine ⟨wrap_ready, wrap, by simp, wrap_checked, rfl, rfl, [(0,0)], wrap_located, ?_, ?_⟩
  · refine ⟨metadata, wrap_linked, fresh 101, [(0,0)], wrap_located, ?_, ?_, ?_, wrap_emissions⟩
    · rw [wrap_report]; exact ⟨rfl,rfl,rfl⟩
    · rw [wrap_report]; exact covered
    · refine ⟨model, ?_⟩
      unfold GeneralNominalCandidates.privateState
      rw [wrap_report]
      exact captured_models 101 wrap rfl
  · rw [wrap_report]
    exact wrap_children.symm

theorem display_exactly_one (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    GeneralNominalCandidates.Survivor registry (context true) displayRoot key children ↔
      key = 1 ∧ children = [displayChild] := by
  constructor
  · intro survivor
    have original := survivor
    obtain ⟨_, declaration, visible, checked, identity, role, bounds, located, prepared, _⟩ := survivor
    have equal := Option.some.inj (display_located.symm.trans located)
    subst bounds
    simp only [List.mem_cons, List.not_mem_nil, or_false] at visible
    rcases visible with rfl | rfl | rfl
    · obtain ⟨_, _, _, other, found, finished, _⟩ := prepared
      have equal := Option.some.inj (display_located.symm.trans found)
      subst other
      rw [int_report] at finished
      cases finished.2.1
    · have keySame : key = 1 := identity.symm
      subst key
      exact ⟨rfl,GeneralNominalCandidates.survivor_children_functional registry registry_checked
        (context true) displayRoot 1 children [displayChild] original display_survivor⟩
    · contradiction
  · rintro ⟨rfl,rfl⟩
    exact display_survivor

end Yulang.GeneralNominalExamples
