import Yulang.GeneralNominalRefreshFork
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics
import Yulang.GeneralNominalGroundExamples

/-! Concrete raw source for a journal-refinement probe. This file alone does
not assert a reachable journal, selected diagnostic or EvidenceNode failure. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement228Source
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralSourceState (equationAtoms equationAtoms_exact)
open CommonNominalFullCarrier

abbrev constructors : Constructors := fun name =>
  some ⟨if name = 0 then [.type,.type] else [],name⟩
abbrev roles : Roles.RoleDecls := fun _ => GeneralDeclarationExamples.outputRole 0
abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun name => if name = 2 then some .emptyRecord else if name = 3 then some .exactEmpty else none
  invariantNominal := fun name => name == 0
  disjoint := by intro name yes; simp_all

abbrev base : GeneralSourceState.State where
  slots := 5
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.var 1) ++ equationAtoms 2 .emptyRecord ++ equationAtoms 3 .top ++
    [.tyLe (.var 4) (.var 2)]
  kinds := 1
  shapes := fun _ => .emptyRecord
  shapes_injective := by intro i j _; exact Subsingleton.elim i j
  heads := fun slot => if slot = 2 then .structural 0 Fin.elim0 else .unresolved
  intervals := []
  heads_sound := by
    intro assignment models slot term recorded
    by_cases two : slot = 2
    · subst slot
      have same : (Core.PresenceGeneration.TyTerm.emptyRecord : Core.PresenceGeneration.TyTerm (Fin 5)) = term := by
        simpa [GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using recorded
      subst term
      exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp
        ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp models).1).1).2
    · simp [two,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 1
  shapes := fun _ => .record []
  shapes_injective := by intro i j _; exact Subsingleton.elim i j
  canonical := by intro _; exact List.Pairwise.nil
  heads := fun slot => if slot = 2 then .structural 0 Fin.elim0 else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases two : slot = 2
    · subst slot
      have same : (Core.PresenceGeneration.TyTerm.emptyRecord : Core.PresenceGeneration.TyTerm (Fin 5)) = term := by
        simpa [GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm] using recorded
      subst term
      exact .head rfl
    · simp [two,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev descriptor (bounds : Fin 5 × Fin 5) : GeneralNominalState.Descriptor 5 :=
  ⟨0,⟨[.type,.type],0⟩,[.type bounds,.type bounds],rfl⟩

abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 0 then some (descriptor (4,2))
    else if slot = 1 then some (descriptor (2,2)) else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · cases Option.some.inj recorded; rfl
    · split at recorded
      · cases Option.some.inj recorded; rfl
      · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases two : slot = 2
    · subst slot; simp at recorded
    · simp [view,two]

abbrev context : GeneralNominalCandidates.Context := ⟨state,interpretation⟩
abbrev root : Occurrence roles := ⟨228,⟨0,fun _ => (0,0),[⟨0,4⟩],by
  intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev foo : Ty := nominal 0 [.inl .emptyRecord,.inl .emptyRecord]
def model (point : Bool) : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source = 0 ∨ source = 1 then foo else if source = 2 then .emptyRecord
    else if source = 3 then .top else if point then .emptyRecord else .exactEmpty,Common.rowEmpty)

theorem lower_fits (point : Bool) : Subtype (model point 4).1 .emptyRecord := by
  cases point
  · exact exactEmpty_below_width
  · exact subtype_refl _

theorem source_models (point : Bool) : GeneralNominalState.Models state (model point) := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    simp only [base,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | rfl
    all_goals first | exact subtype_refl _ | exact lower_fits point
  · intro slot term recorded
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj recorded.symm
      subst term; exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [state,base,two,GeneralSourceState.Head.equation] at recorded
  · intro pair member; cases member
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot
      cases Option.some.inj recorded
      refine ⟨[.inl .emptyRecord,.inl .emptyRecord],.cons ?_ (.cons ?_ .nil),subtype_refl _,subtype_refl _⟩
      all_goals exact ⟨lower_fits point,subtype_refl _⟩
    · by_cases one : slot = 1
      · subst slot
        cases Option.some.inj recorded
        exact ⟨[.inl .emptyRecord,.inl .emptyRecord],.cons ⟨subtype_refl _,subtype_refl _⟩
          (.cons ⟨subtype_refl _,subtype_refl _⟩ .nil),subtype_refl _,subtype_refl _⟩
      · simp [state,zero,one] at recorded

abbrev snapshot := state
abbrev modelLow := model false
abbrev modelHigh := model true

theorem alias_zero (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 0).1 (m 1).1 := by
  exact ⟨valid.1.1 (.tyLe (.var 0) (.var 1)) (by simp [base,equationAtoms]),
    valid.1.1 (.tyLe (.var 1) (.var 0)) (by simp [base,equationAtoms])⟩

theorem width_two (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 2).1 .emptyRecord :=
  valid.1.2.1 2 .emptyRecord rfl

theorem top_three (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 3).1 .top := by
  exact ⟨valid.1.1 (.tyLe (.var 3) .top) (by simp [base,equationAtoms]),
    valid.1.1 (.tyLe .top (.var 3)) (by simp [base,equationAtoms])⟩

theorem lower_width (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot m) : Subtype (m 4).1 (m 2).1 :=
  valid.1.1 (.tyLe (.var 4) (.var 2)) (by simp [base,equationAtoms])

theorem root_fixed (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 0).1 foo := by
  obtain ⟨arguments,fits,equal⟩ := valid.2.1 (1 : Fin 5) (descriptor (2,2)) rfl
  change GeneralNominalState.FitsAll base m [.type (2,2),.type (2,2)] arguments at fits
  cases fits with
  | @cons parameter a parameters rest first tail =>
    cases tail with
    | @cons _ b _ rest second tail =>
      cases tail
      cases a with
      | inr => cases first
      | inl a =>
        cases b with
        | inr => cases second
        | inl b =>
          have width := width_two m valid
          have one : Equivalent a .emptyRecord := ⟨subtype_trans first.2 width.1,subtype_trans width.2 first.1⟩
          have two : Equivalent b .emptyRecord := ⟨subtype_trans second.2 width.1,subtype_trans width.2 second.1⟩
          have nominal := GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons one (.cons two .nil))
          exact ⟨subtype_trans (alias_zero m valid).1 (subtype_trans equal.1 nominal.1),
            subtype_trans (subtype_trans nominal.2 equal.2) (alias_zero m valid).2⟩

open GeneralNominalRecursiveInspection GeneralNominalGroundAccessibility GeneralNominalFiniteMeaning
open GeneralNominalOriginTerms GeneralNominalReadbackFunctionality GeneralNominalCompoundReadback
abbrev widthTerm : Expr Nat := .node (.structural (.record [])) Fin.elim0
abbrev fooTerm : Expr Nat := .node (.nominal 0 2) (fun _ => widthTerm)
abbrev labels : List Pattern := [.app 0 [.app 2 [],.app 2 []]]

theorem closed : ClosedTerm context labels[0] fooTerm := by
  refine ⟨?_,?_,?_⟩
  · simp [labels,normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation,
      quote,List.ofFn_succ,arity,GeneralNormalizedObservation.Shape.arity]
  · simp [Expr.leaves,List.ofFn_succ,arity,GeneralNormalizedObservation.Shape.arity]
  · exact ⟨trivial,fun _ => ⟨List.Pairwise.nil,fun i => Fin.elim0 i⟩⟩

theorem ground : GroundRoots context root labels := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  refine ⟨fooTerm,?_,?_⟩
  · simpa only [zero] using closed
  · intro m valid
    simpa [root,foo,denote,build,fooTerm,widthTerm,shapeValue,
      GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm,
      GeneralNormalizedObservation.Shape.arity,List.ofFn_succ,arity,
      Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using root_fixed m valid

theorem source_bound (identity : Nat) (member : identity ∈ GeneralNominalState.sources snapshot) : identity ≤ 4 := by
  simp only [GeneralNominalState.sources,base,List.mem_append,List.mem_ofFn,List.not_mem_nil,
    List.flatMap_nil,or_false] at member
  rcases member with ⟨slot,rfl⟩ | ⟨slot,rfl⟩ <;> have bound := slot.isLt <;> omega

theorem metadata (registry : Registry) (same : registry.constructors = constructors) :
    GeneralNominalRecursiveCandidates.Metadata registry context := by
  refine ⟨same,?_⟩
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have equal : primitive = .emptyRecord := Option.some.inj recorded |>.symm
    subst primitive
    exact ⟨⟨[],2⟩,by simp [same,constructors],rfl⟩
  · by_cases three : name = 3
    · subst name
      have equal : primitive = .exactEmpty := Option.some.inj recorded |>.symm
      subst primitive
      exact ⟨⟨[],3⟩,by simp [same,constructors],rfl⟩
    · simp [two,three] at recorded

theorem initial_source (registry : Registry) (same : registry.constructors = constructors)
    (sameRoles : registry.roles = roles) :
    GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨sameRoles,metadata registry same,?_,(by intro _ _ _; exact subtype_refl _),?_,rfl⟩
  · constructor
    · intro index
      constructor <;> exact GeneralNominalAllocationSupport.slot_source snapshot 0
    · intro output member
      cases List.mem_singleton.mp member
      exact GeneralNominalAllocationSupport.slot_source snapshot 4
  · intro identity member
    exact source_bound identity member

theorem root_point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2 := fun _ => rfl

theorem low_value : (modelLow 4).1 = .exactEmpty := rfl
theorem high_value : (modelHigh 4).1 = .emptyRecord := rfl
theorem source_variation : GeneralNominalState.Models snapshot modelLow ∧
    GeneralNominalState.Models snapshot modelHigh ∧ ¬ Equivalent (modelLow 4).1 (modelHigh 4).1 :=
  ⟨source_models false,source_models true,exactEmpty_not_equivalent_width⟩

end Yulang.GeneralDictionaryJournalRefinement228Source
