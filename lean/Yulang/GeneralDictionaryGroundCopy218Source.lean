import Yulang.GeneralDictionaryLooseVariant217
import Yulang.GeneralDictionaryDefaultComposition211
import Yulang.GeneralDeclarationExamples

set_option backward.isDefEq.respectTransparency false

/-! The cycle-217 source layout, with a loose descriptor at 6 equated to its
exact copy at 7. Groundness is universal over source models. This module proves
only source formation and initial reachability; it makes no stability or
selected-child assertion. All roles in this fixture have no named outputs. -/

namespace Yulang.GeneralDictionaryGroundCopy218Source
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (constructors bareRole binaryRole)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralDictionaryLooseVariant217

abbrev roles : Roles.RoleDecls := fun role => if role = 0 then bareRole else binaryRole
abbrev child : Clause := ⟨0,1,[.var 0,.var 1],[]⟩
abbrev parent : Declaration := ⟨0,0,[.app 5 [.var 0,.var 1]],[child],[],[]⟩
abbrev leaf : Declaration := ⟨1,1,[.var 0,.var 0],[],[],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[parent,leaf]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry

theorem parent_checked : DeclarationChecked constructors roles parent := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,bareRole,binaryRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member
    unfold ConservativeSmaller; decide +kernel
  · intro clause member capture; cases List.mem_singleton.mp member
    constructor
    · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
    · intro name
      simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem leaf_checked : DeclarationChecked constructors roles leaf := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,bareRole,binaryRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

theorem source_checked : Checked sourceRegistry := by
  refine ⟨by simp,?_⟩
  intro declaration member
  rcases List.mem_cons.mp member with rfl | member
  · exact parent_checked
  · cases List.mem_singleton.mp member; exact leaf_checked

theorem checked : Checked registry := GeneralNominalCenteredHeadAllocEncoding.registry_checked source_checked

abbrev equations : List (Fin 8 × TyTerm (Fin 8)) :=
  [(0,.bottom),(1,.top),(2,.variant 0 (.var 0)),(3,.variant 0 (.var 1)),
   (4,.variant 0 (.base .int)),(5,.variant 0 (.base .bool)),(6,.var 7)]
abbrev atoms := equations.flatMap fun p => GeneralSourceState.equationAtoms p.1 p.2

abbrev base : GeneralSourceState.State where
  slots := 8
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := atoms
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ h; cases h
  intervals_sound := by intro _ _ _ h; cases h

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 1
  shapes := fun _ => .variant 0
  shapes_injective := fun _ _ _ => Subsingleton.elim _ _
  canonical := fun _ => trivial
  heads := fun slot => if slot = 2 then .structural 0 (fun _ => 0)
    else if slot = 3 then .structural 0 (fun _ => 1) else .deferred .unresolved
  checked := by
    intro slot term recorded
    split at recorded
    · rename_i same
      subst slot
      cases Option.some.inj recorded
      exact .ordinary (by simp [atoms,equations,GeneralSourceState.equationAtoms,GeneralNormalizedObservation.Shape.term])
        (by simp [atoms,equations,GeneralSourceState.equationAtoms,GeneralNormalizedObservation.Shape.term])
    · split at recorded
      · rename_i same
        subst slot
        cases Option.some.inj recorded
        exact .ordinary (by simp [atoms,equations,GeneralSourceState.equationAtoms,GeneralNormalizedObservation.Shape.term])
          (by simp [atoms,equations,GeneralSourceState.equationAtoms,GeneralNormalizedObservation.Shape.term])
      · cases recorded

abbrev loose : GeneralNominalState.Descriptor 8 := ⟨5,⟨[.type,.type],5⟩,[.type (2,3),.type (2,3)],rfl⟩
abbrev exactCopy : GeneralNominalState.Descriptor 8 := ⟨5,⟨[.type,.type],5⟩,[.type (4,4),.type (5,5)],rfl⟩
abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 6 then some loose else if slot = 7 then some exactCopy else none
  catalogue := by
    intro slot d found
    split at found
    · cases Option.some.inj found; rfl
    · split at found
      · cases Option.some.inj found; rfl
      · cases found
  bodies_opaque := by
    intro slot d found
    split at found
    · rename_i same; subst slot; rfl
    · split at found
      · rename_i same; subst slot; rfl
      · cases found
  seed := 7

abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun name => if name = 2 then some (.scalar .int) else if name = 3 then some (.scalar .bool) else none
  invariantNominal := fun name => name == 5
  disjoint := by intro name yes; simp_all
abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,interpretation⟩
abbrev root : Occurrence roles := ⟨0,⟨0,fun _ => (6,6),[],by intro _ h; cases h⟩⟩
abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial context root

def sourceValue : Nat → Ty
  | 0 => .bottom
  | 1 => .top
  | 2 => low
  | 3 => high
  | 4 => first
  | 5 => second
  | 6 | 7 => nominal 5 [.inl first,.inl second]
  | _ => .bottom

def witness : Assignment := fun source => (sourceValue source,Common.rowEmpty)

theorem base_models : GeneralNominalCommonBridge.Models base witness := by
  refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
  intro atom member
  simp only [atoms,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
    GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact subtype_refl _

theorem source_model : GeneralNominalState.Models snapshot witness := by
  refine ⟨base_models,?_,by intro _ h; cases h⟩
  intro slot descriptor found
  change (if slot = 6 then some loose else if slot = 7 then some exactCopy else none) = some descriptor at found
  split at found
  · rename_i same
    subst slot
    cases Option.some.inj found
    exact ⟨[.inl first,.inl second],.cons fits_first (.cons fits_second .nil),⟨subtype_refl _,subtype_refl _⟩⟩
  · split at found
    · rename_i same
      subst slot
      cases Option.some.inj found
      exact ⟨[.inl first,.inl second],.cons ⟨subtype_refl _,subtype_refl _⟩
        (.cons ⟨subtype_refl _,subtype_refl _⟩ .nil),⟨subtype_refl _,subtype_refl _⟩⟩
    · cases found


theorem equation (model : Assignment) (valid : GeneralNominalState.Models snapshot model)
    (slot : Fin 8) (term : TyTerm (Fin 8)) (member : (slot,term) ∈ equations) :
    Equivalent (model slot.val).1 (term.eval CommonNominalFullCarrier.model
      (GeneralNominalCommonBridge.assignment base model)) := by
  constructor
  · exact valid.1.1 _ (List.mem_flatMap.mpr ⟨(slot,term),member,List.mem_cons_self⟩)
  · exact valid.1.1 _ (List.mem_flatMap.mpr ⟨(slot,term),member,List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)

theorem first_fixed (model : Assignment) (valid : GeneralNominalState.Models snapshot model) :
    Equivalent (model 4).1 first := equation model valid 4 (.variant 0 (.base .int)) (by simp [equations])
theorem second_fixed (model : Assignment) (valid : GeneralNominalState.Models snapshot model) :
    Equivalent (model 5).1 second := equation model valid 5 (.variant 0 (.base .bool)) (by simp [equations])
theorem copy_equal (model : Assignment) (valid : GeneralNominalState.Models snapshot model) :
    Equivalent (model 6).1 (model 7).1 := equation model valid 6 (.var 7) (by simp [equations])

theorem nominal_pair_congr {a b c d : Ty} (one : Equivalent a c) (two : Equivalent b d) :
    Equivalent (nominal 5 [.inl a,.inl b]) (nominal 5 [.inl c,.inl d]) := by
  have forward {a b c d : Ty} (one : Equivalent a c) (two : Equivalent b d) :
      Subtype (nominal 5 [.inl a,.inl b]) (nominal 5 [.inl c,.inl d]) := by
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,rfl,?_⟩
    intro index x y firstFound secondFound
    cases index with
    | zero => cases Option.some.inj firstFound; cases Option.some.inj secondFound; exact one
    | succ index =>
      cases index with
      | zero => cases Option.some.inj firstFound; cases Option.some.inj secondFound; exact two
      | succ index => cases firstFound
  exact ⟨forward one two,forward ⟨one.2,one.1⟩ ⟨two.2,two.1⟩⟩

theorem root_fixed (model : Assignment) (valid : GeneralNominalState.Models snapshot model) :
    Equivalent (model 6).1 (nominal 5 [.inl first,.inl second]) := by
  obtain ⟨values,fits,equal⟩ := valid.2.1 7 exactCopy rfl
  change GeneralNominalState.FitsAll base model [.type (4,4),.type (5,5)] values at fits
  cases fits with
  | @cons _ a _ rest fitA remaining =>
    cases remaining with
    | @cons _ b _ tail fitB remaining =>
      cases remaining
      cases a with
      | inr => cases fitA
      | inl a =>
        cases b with
        | inr => cases fitB
        | inl b =>
          have aEq := first_fixed model valid
          have bEq := second_fixed model valid
          have copies := nominal_pair_congr
            ⟨subtype_trans fitA.2 aEq.1,subtype_trans aEq.2 fitA.1⟩
            ⟨subtype_trans fitB.2 bEq.1,subtype_trans bEq.2 fitB.1⟩
          have roots := copy_equal model valid
          exact ⟨subtype_trans roots.1 (subtype_trans equal.1 copies.1),
            subtype_trans copies.2 (subtype_trans equal.2 roots.2)⟩

theorem metadata : GeneralNominalRecursiveCandidates.Metadata sourceRegistry context := by
  refine ⟨rfl,?_⟩
  intro name primitive found
  change (if name = 2 then some (.scalar .int) else if name = 3 then some (.scalar .bool) else none) = some primitive at found
  split at found
  · rename_i same; subst name; cases Option.some.inj found; exact ⟨_,rfl,rfl⟩
  · split at found
    · rename_i same; subst name; cases Option.some.inj found; exact ⟨_,rfl,rfl⟩
    · cases found

theorem source : GeneralNominalSourceFormation.InitialSource sourceRegistry context root where
  roles_agree := rfl
  metadata := metadata
  linked := ⟨by intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ],by intro _ h; cases h⟩
  intervals := fun _ _ _ => subtype_refl _
  below_seed := by
    intro identity member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    change identity ≤ 7
    omega
  unallocated := rfl

abbrev scalarTerm (scalar : Inference.Base) : GeneralNominalOriginTerms.Expr Nat :=
  .node (.scalar scalar) Fin.elim0
abbrev variantTerm (scalar : Inference.Base) : GeneralNominalOriginTerms.Expr Nat :=
  .node (.structural (.variant 0)) (fun _ => scalarTerm scalar)
abbrev rootTerm : GeneralNominalOriginTerms.Expr Nat :=
  .node (.nominal 5 2) (fun index => if index.val = 0 then variantTerm .int else variantTerm .bool)
abbrev rootPattern : Pattern := .app 5 [.variant 0 (.app 2 []),.variant 0 (.app 3 [])]

theorem root_closed : GeneralNominalGroundAccessibility.ClosedTerm context rootPattern rootTerm := by
  refine ⟨?_,?_,?_⟩
  · simp [variantTerm,scalarTerm,normalize,normalizeArgs,
      GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames,
      GeneralNominalCompoundReadback.quote,List.ofFn_succ,GeneralNominalOriginTerms.arity]
  · simp [variantTerm,scalarTerm,GeneralNominalOriginTerms.Expr.leaves,
      List.ofFn_succ,GeneralNominalOriginTerms.arity]
  · refine ⟨trivial,?_⟩
    intro index
    change GeneralNominalReadbackFunctionality.Canonical (if index.val = 0 then variantTerm .int else variantTerm .bool)
    split <;> exact ⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩

theorem root_denote : GeneralNominalFiniteMeaning.denote (fun _ => .bottom) rootTerm =
    nominal 5 [.inl first,.inl second] := by
  simp [variantTerm,scalarTerm,GeneralNominalFiniteMeaning.denote,
    GeneralNominalFiniteMeaning.build,List.ofFn_succ,GeneralNominalOriginTerms.arity,
    GeneralNominalRecursiveInspection.shapeValue,GeneralNormalizedObservation.Shape.term,
    TyTerm.eval,first,second,CommonNominalFullCarrier.model]

theorem ground : GeneralNominalGroundAccessibility.GroundRoots context root [rootPattern] := by
  refine ⟨rfl,?_⟩
  intro index
  change Fin 1 at index
  have zero : index = 0 := Subsingleton.elim _ _
  subst index
  refine ⟨rootTerm,root_closed,?_⟩
  intro model valid
  rw [root_denote]
  exact root_fixed model valid

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry interpretation := by
  constructor
  · intro declaration member
    rcases List.mem_cons.mp member with rfl | member
    · simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
        GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
        GeneralNominalCenteredHeadWFSource.ConstructorUse]
    · cases List.mem_singleton.mp member
      simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
        GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered]
  · intro role name body found
    by_cases zero : role = 0 <;> simp [roles,zero,bareRole,binaryRole] at found

theorem initial_source : (GeneralDictionaryDefaultBoundary208.boundary roles).Initial sourceRegistry root start :=
  ⟨context,[rootPattern],source,(fun _ => rfl),ground,coverage,rfl⟩
theorem reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root start :=
  ⟨start,initial_source,.refl⟩
theorem inhabited : GeneralNominalCenteredHeadMatStepJournal.Models start witness :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr source_model


theorem source_model_of_values (given : Assignment)
    (values : ∀ identity, identity < 8 → (given identity).1 = sourceValue identity) :
    GeneralNominalState.Models snapshot given := by
  have baseGiven : GeneralNominalCommonBridge.Models base given := by
    refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
    intro atom member
    simp only [atoms,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
      GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change Subtype _ _
      dsimp only [TyTerm.eval,GeneralNominalCommonBridge.assignment]
      change Subtype _ _
      simp only [show (0 : Fin 8).val = 0 from rfl,show (1 : Fin 8).val = 1 from rfl,
        show (2 : Fin 8).val = 2 from rfl,show (3 : Fin 8).val = 3 from rfl,
        show (4 : Fin 8).val = 4 from rfl,show (5 : Fin 8).val = 5 from rfl,
        show (6 : Fin 8).val = 6 from rfl,show (7 : Fin 8).val = 7 from rfl,
        values 0 (by decide),values 1 (by decide),values 2 (by decide),values 3 (by decide),
        values 4 (by decide),values 5 (by decide),values 6 (by decide),values 7 (by decide)]
      exact subtype_refl _
  refine ⟨baseGiven,?_,by intro _ h; cases h⟩
  intro slot descriptor found
  change (if slot = 6 then some loose else if slot = 7 then some exactCopy else none) = some descriptor at found
  split at found
  · rename_i same
    subst slot
    cases Option.some.inj found
    refine ⟨[.inl first,.inl second],.cons ?_ (.cons ?_ .nil),?_⟩
    · change Subtype (given 2).1 first ∧ Subtype first (given 3).1
      rw [values 2 (by decide),values 3 (by decide)]
      exact fits_first
    · change Subtype (given 2).1 second ∧ Subtype second (given 3).1
      rw [values 2 (by decide),values 3 (by decide)]
      exact fits_second
    · change Equivalent (given 6).1 _
      rw [values 6 (by decide)]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · split at found
    · rename_i same
      subst slot
      cases Option.some.inj found
      refine ⟨[.inl first,.inl second],.cons ?_ (.cons ?_ .nil),?_⟩
      · change Subtype (given 4).1 first ∧ Subtype first (given 4).1
        rw [values 4 (by decide)]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · change Subtype (given 5).1 second ∧ Subtype second (given 5).1
        rw [values 5 (by decide)]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · change Equivalent (given 7).1 _
        rw [values 7 (by decide)]
        exact ⟨subtype_refl _,subtype_refl _⟩
    · cases found

end Yulang.GeneralDictionaryGroundCopy218Source
