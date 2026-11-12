import Yulang.GeneralDictionaryBranchLeaf
import Yulang.GeneralDeclarationExamples

namespace Yulang.GeneralNominalBranchExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalState
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarationExamples (roles constructors)
open CommonNominalFullCarrier

abbrev base : GeneralSourceState.State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro model valid slot term recorded; cases recorded
  intervals_sound := by intro model valid pair member; cases member
abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro slot term recorded; cases recorded
abbrev parent : Descriptor 3 := ⟨5,⟨[.type,.type],5⟩,[.type (1,1),.type (2,2)],rfl⟩
abbrev left : Descriptor 3 := ⟨2,⟨[],2⟩,[],rfl⟩
abbrev right : Descriptor 3 := ⟨3,⟨[],3⟩,[],rfl⟩
abbrev state : State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => some (if slot = 0 then parent else if slot = 1 then left else right)
  catalogue := by
    intro slot descriptor recorded
    cases Option.some.inj recorded
    split <;> simp [constructors]
    split <;> simp
  bodies_opaque := by intros; rfl
abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun _ => none
  invariantNominal := fun _ => true
  disjoint := by intros; rfl
abbrev context : Context := ⟨state,interpretation⟩
abbrev declaration : Declaration := ⟨40,0,[.app 5 [.app 2 [],.app 3 []]],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev demand : GeneralSourceState.Demand roles := ⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨100,demand⟩
abbrev model : GeneralNominalCommonBridge.Assignment := fun id =>
  (if id = 0 then nominal 5 [.inl (nominal 2 []),.inl (nominal 3 [])]
   else if id = 1 then nominal 2 [] else nominal 3 [],Common.rowEmpty)

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
  · exact PresenceNormalForm.all_nil _ _
  · intro slot term recorded; cases recorded
  · intro pair member; cases member
  · intro slot descriptor recorded
    have positions : slot = 0 ∨ slot = 1 ∨ slot = 2 := by
      have bound : slot.val < 3 := slot.isLt
      have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
      rcases cases with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases positions with rfl | rfl | rfl
    · cases Option.some.inj recorded
      exact ⟨[.inl (nominal 2 []),.inl (nominal 3 [])],
        .cons ⟨subtype_refl _,subtype_refl _⟩ (.cons ⟨subtype_refl _,subtype_refl _⟩ .nil),
        ⟨subtype_refl _,subtype_refl _⟩⟩
    · cases Option.some.inj recorded
      exact ⟨[],.nil,⟨subtype_refl _,subtype_refl _⟩⟩
    · cases Option.some.inj recorded
      exact ⟨[],.nil,⟨subtype_refl _,subtype_refl _⟩⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · simp
  · simp
  · simp
  · simp

abbrev fork : GeneralNominalBranchFacts.Fork state 0 0 Fin.elim0 Fin.elim0 0 where
  left := 1
  right := 2
  descriptor := parent
  recorded := rfl
  parameters := rfl
  one := .leaf 1 left rfl rfl
  two := .leaf 2 right rfl rfl
abbrev shape : GeneralDictionaryBranchLeaf.BranchLeafShape context root declaration where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := 0
  leftArity := 0
  rightArity := 0
  names := Fin.elim0
  distinct := by intro i; exact Fin.elim0 i
  inputs := rfl
  bounds := Fin.elim0
  fork := fork
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,interpretation,GeneralNominalBranchFacts.Fork.query,GeneralNominalSpineFacts.Spine.query]
  located := rfl

theorem actual_branch : BranchModels registry context root declaration checked [(0,0)] model :=
  GeneralDictionaryBranchLeaf.branch_models context registry root declaration checked shape model state_models


/-- The fork's query is not any unary-spine query at this actual root. -/
theorem not_unary_spine {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (spine : GeneralNominalSpineFacts.Spine state names bounds 0) :
    spine.query ≠ fork.query := by
  intro equal
  cases spine with
  | leaf slot descriptor recorded parameters =>
    change some parent = some descriptor at recorded
    cases Option.some.inj recorded
    cases n with
    | zero => simp [GeneralNominalSpineFacts.Spine.query,GeneralNominalBranchFacts.Fork.query] at equal
    | succ n => simp [GeneralNominalSpineFacts.Spine.query,GeneralNominalBranchFacts.Fork.query,List.ofFn_succ] at equal
  | wrap slot child descriptor recorded parameters rest =>
    change some parent = some descriptor at recorded
    cases Option.some.inj recorded
    have wrong := congrArg List.length parameters
    simp at wrong

/-- A concrete inhabitant of both source and derived private branch models. -/
theorem inhabited_branch : GeneralNominalState.Models state model ∧
    BranchModels registry context root declaration checked [(0,0)] model :=
  ⟨state_models,actual_branch⟩
end Yulang.GeneralNominalBranchExample
