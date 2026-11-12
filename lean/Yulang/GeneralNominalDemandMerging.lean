import Yulang.GeneralNominalRefinements

/-! Same-input merging uses actual source observations, never intersection of
endpoint supports. Unknown provenance defers this update. Output preservation
is stated for a common associated interpretation; its dictionary bridge remains
explicit rather than being inferred from independent dictionary witnesses. -/
namespace Yulang.GeneralNominalDemandMerging

open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes)
open CommonNominalFullCarrier
open GeneralSourceDictionaries (Occurrence)

inductive All₂ (relation : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ relation [] []
  | cons : relation a b → All₂ relation as bs → All₂ relation (a :: as) (b :: bs)

structure Site (roles : Roles.RoleDecls) where
  occurrence : Occurrence roles
  inputs : List (Option Origin)
  arity : inputs.length = (roles occurrence.demand.role).arity

def pointSite (occurrence : Occurrence roles) : Site roles where
  occurrence := occurrence
  inputs := List.ofFn fun index =>
    let bounds := occurrence.demand.arguments index
    if bounds.1 = bounds.2 then some (.source bounds.1) else none
  arity := List.length_ofFn

def SameOrigin (models : Assignment → Prop) (first last : Origin) : Prop :=
  ∀ model, models model →
    (∃ value, Observes model first value) ∧ (∃ value, Observes model last value) ∧
    ∀ a b, Observes model first a → Observes model last b → Equivalent a b

def Related (models : Assignment → Prop) (first last : Option Origin) : Prop :=
  ∃ a b, first = some a ∧ last = some b ∧ SameOrigin models a b

def SameInputs (models : Assignment → Prop) (first last : Site roles) : Prop :=
  first.occurrence.demand.role = last.occurrence.demand.role ∧ All₂ (Related models) first.inputs last.inputs

def Denotes (model : Assignment) (site : Site roles) (values : List Ty) : Prop :=
  All₂ (fun ref value => ∃ origin, ref = some origin ∧ Observes model origin value) site.inputs values

theorem source_same (models : Assignment → Prop) (identity : Nat) :
    SameOrigin models (.source identity) (.source identity) := by
  intro model _
  refine ⟨⟨_,.source identity⟩,⟨_,.source identity⟩,?_⟩
  intro a b ha hb
  cases ha; cases hb; exact ⟨subtype_refl _,subtype_refl _⟩

theorem same_inputs_denote (models : Assignment → Prop) (first last : Site roles)
    (same : SameInputs models first last) (model : Assignment) (valid : models model)
    (a b : List Ty) (left : Denotes model first a) (right : Denotes model last b) :
    All₂ Equivalent a b := by
  have related := same.2
  unfold Denotes at left right
  generalize first.inputs = xs at related left
  generalize last.inputs = ys at related right
  induction related generalizing a b with
  | nil => cases left; cases right; exact .nil
  | cons related rest ih =>
      cases left with
      | cons head tail =>
        cases right with
        | cons other suffix =>
          obtain ⟨x,y,hx,hy,equal⟩ := related
          obtain ⟨x',hx',seen⟩ := head
          obtain ⟨y',hy',found⟩ := other
          have ex := Option.some.inj (hx.symm.trans hx'); subst x'
          have ey := Option.some.inj (hy.symm.trans hy'); subst y'
          exact .cons ((equal model valid).2.2 _ _ seen found) (ih _ _ tail suffix)

theorem different_inputs_prevent_merge (models : Assignment → Prop) (first last : Site roles)
    (model : Assignment) (valid : models model) (a b : List Ty)
    (left : Denotes model first a) (right : Denotes model last b)
    (different : ¬ All₂ Equivalent a b) : ¬ SameInputs models first last :=
  fun same => different (same_inputs_denote models first last same model valid a b left right)

theorem unknown_input_prevents_merge (models : Assignment → Prop) (first last : Site roles)
    (unknown : none ∈ first.inputs) : ¬ SameInputs models first last := by
  intro same
  have all : ∀ entry ∈ first.inputs, entry ≠ none := by
    have relation := same.2
    generalize first.inputs = xs at relation ⊢
    generalize last.inputs = ys at relation
    induction relation with
    | nil => simp
    | cons head _ ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨a,b,equal,_,_⟩ := head
        rw [equal]; simp
      · exact ih entry member
  exact all none unknown rfl

def outputAtoms (first last : Site roles) : List (PresenceNormalForm.Atom Nat) :=
  first.occurrence.demand.outputs.flatMap fun a => last.occurrence.demand.outputs.flatMap fun b =>
    if a.name = b.name then GeneralNominalAllocation.equations a.target (.var b.target) else []

theorem output_atoms_exact (first last : Site roles) (model : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last) ↔
      ∀ a ∈ first.occurrence.demand.outputs, ∀ b ∈ last.occurrence.demand.outputs, a.name = b.name →
        Equivalent (model a.target).1 (model b.target).1 := by
  simp only [outputAtoms,PresenceNormalForm.All,List.mem_flatMap]
  constructor
  · intro valid a ha b hb same
    apply (GeneralNominalCaptureMerges.equations_exact model a.target (.var b.target)).mp
    intro atom member
    exact valid atom ⟨a,ha,b,hb,by simpa only [same,ite_true] using member⟩
  · intro valid atom member
    obtain ⟨a,ha,b,hb,member⟩ := member
    by_cases same : a.name = b.name
    · have atoms := (GeneralNominalCaptureMerges.equations_exact model a.target (.var b.target)).mpr (valid a ha b hb same)
      exact atoms atom (by simpa only [same,ite_true] using member)
    · simp [same] at member

structure AssociatedMeaning where
  value : Nat → List Ty → Nat → Ty
  congruent : ∀ role a b name, All₂ Equivalent a b → Equivalent (value role a name) (value role b name)

/-- The output facet required of dictionary evidence, not a replacement for
the dictionary tree, declaration matching, or associated-child evidence. -/
def DictionaryOutputs (meaning : AssociatedMeaning) (model : Assignment) (site : Site roles) : Prop :=
  ∃ values, Denotes model site values ∧ ∀ output ∈ site.occurrence.demand.outputs,
    Equivalent (model output.target).1 (meaning.value site.occurrence.demand.role values output.name)

theorem dictionary_outputs_preserved (models : Assignment → Prop) (first last : Site roles)
    (same : SameInputs models first last) (meaning : AssociatedMeaning) (model : Assignment)
    (valid : models model) (left : DictionaryOutputs meaning model first) (right : DictionaryOutputs meaning model last) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last) := by
  obtain ⟨a,ad,ao⟩ := left
  obtain ⟨b,bd,bo⟩ := right
  have inputs := same_inputs_denote models first last same model valid a b ad bd
  apply (output_atoms_exact first last model).mpr
  intro x hx y hy name
  have values := meaning.congruent first.occurrence.demand.role a b x.name inputs
  have one := ao x hx
  have two := bo y hy
  rw [← same.1,← name] at two
  exact ⟨subtype_trans one.1 (subtype_trans values.1 two.2),
    subtype_trans two.1 (subtype_trans values.2 one.2)⟩

theorem merge_preserves_dictionary_models (state : GeneralNominalState.State)
    (first last : Site roles) (same : SameInputs (GeneralNominalState.Models state) first last)
    (meaning : AssociatedMeaning) (model : Assignment) (valid : GeneralNominalState.Models state model)
    (left : DictionaryOutputs meaning model first) (right : DictionaryOutputs meaning model last) :
    GeneralNominalState.Models (GeneralNominalState.extend state [] (outputAtoms first last)) model :=
  (GeneralNominalState.extend_models ..).mpr
    ⟨valid,dictionary_outputs_preserved _ first last same meaning model valid left right⟩

/-- Checked supplies local associated determination once actual captures and
the child associated interpretation agree. The source/evidence bridge must
establish these premises rather than erase them. -/
theorem checked_associated_equation (checked : GeneralDeclarations.DeclarationChecked constructors roles declaration)
    (associated : GeneralDeclarations.Associated) (first last : Nat → GeneralDeclarationPatterns.Pattern)
    (head : GeneralDeclarations.CapturesAgree declaration first last)
    (left : GeneralDeclarations.SatisfiesOutputs associated declaration first)
    (right : GeneralDeclarations.SatisfiesOutputs associated declaration last)
    (equation : GeneralDeclarations.Equation) (present : equation ∈ declaration.associated)
    (interpret : GeneralDeclarationPatterns.Pattern → Ty) (model : Assignment) (a b : Nat)
    (one : Equivalent (model a).1 (interpret ((GeneralDeclarationPatterns.normalize equation.rhs).subst first)))
    (two : Equivalent (model b).1 (interpret ((GeneralDeclarationPatterns.normalize equation.rhs).subst last))) :
    Equivalent (model a).1 (model b).1 := by
  have equal := GeneralDeclarations.capture_determines_associated checked associated first last head left right equation present
  rw [equal] at one
  exact ⟨subtype_trans one.1 two.2,subtype_trans two.1 one.2⟩

end Yulang.GeneralNominalDemandMerging
