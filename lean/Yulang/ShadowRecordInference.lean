import Yulang.ShadowSemanticRecords
import Yulang.InferenceModelMap
import Yulang.RowFlowSchemes

/-!
# Preservation of source typing after hidden-field equality

The original type constructors and source typing rules are unchanged.
Every earlier comparison, formula instance and closed source typing survives.
The maps below do not claim that no new typing becomes available.
-/

namespace Yulang.ShadowRecordInference

open Inference
open StructuralBase (Ty)

universe u

variable {Row : Type u}

def legacyMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    ModelMap (StructuralBase.model Row empty join leRow) (ShadowSemanticRecords.model Row empty join leRow) where
  value := id
  row := id
  base _ := rfl
  bottom := rfl
  top := rfl
  union _ _ := rfl
  inter _ _ := rfl
  pair _ _ := rfl
  emptyRecord := rfl
  record _ _ _ := rfl
  variant _ _ := rfl
  arrow _ _ _ _ := rfl
  empty := rfl
  join _ _ := rfl
  subtype := ShadowSemanticRecords.old_subtype
  subrow proof := proof

/-- Every decision-38 typing remains available after adding exactly the
rigid-target tail rule from decision 39. -/
def congruenceMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    ModelMap (SemanticRecords.model Row empty join leRow)
      (ShadowSemanticRecords.model Row empty join leRow) where
  value := id
  row := id
  base _ := rfl
  bottom := rfl
  top := rfl
  union _ _ := rfl
  inter _ _ := rfl
  pair _ _ := rfl
  emptyRecord := rfl
  record _ _ _ := rfl
  variant _ _ := rfl
  arrow _ _ _ _ := rfl
  empty := rfl
  join _ _ := rfl
  subtype := ShadowSemanticRecords.semantic_subtype
  subrow proof := proof

/-- The identity on values and rows preserves all decision-39 comparisons. -/
def rigidMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    ModelMap (RigidSemanticRecords.model Row empty join leRow)
      (ShadowSemanticRecords.model Row empty join leRow) where
  value := id
  row := id
  base _ := rfl
  bottom := rfl
  top := rfl
  union _ _ := rfl
  inter _ _ := rfl
  pair _ _ := rfl
  emptyRecord := rfl
  record _ _ _ := rfl
  variant _ _ := rfl
  arrow _ _ _ _ := rfl
  empty := rfl
  join _ _ := rfl
  subtype := ShadowSemanticRecords.rigid_subtype
  subrow proof := proof

theorem rigid_formula_preserved (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (formula : Formula α) (assignment : α → Ty Row × Row)
    (held : formula.Holds (RigidSemanticRecords.model Row empty join leRow) assignment) :
    formula.Holds (ShadowSemanticRecords.model Row empty join leRow) assignment :=
  (rigidMap empty join leRow).formula_preserved formula assignment held

theorem rigid_closed_typing_preserved (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (expression : Expr) (result : Ty Row × Row)
    (typed : Typing (RigidSemanticRecords.model Row empty join leRow) [] expression result) :
    Typing (ShadowSemanticRecords.model Row empty join leRow) [] expression result :=
  (rigidMap empty join leRow).closed_typing_preserved expression result typed

theorem congruence_formula_preserved (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (formula : Formula α) (assignment : α → Ty Row × Row)
    (held : formula.Holds (SemanticRecords.model Row empty join leRow) assignment) :
    formula.Holds (ShadowSemanticRecords.model Row empty join leRow) assignment :=
  (congruenceMap empty join leRow).formula_preserved formula assignment held

theorem congruence_closed_typing_preserved (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (expression : Expr) (result : Ty Row × Row)
    (typed : Typing (SemanticRecords.model Row empty join leRow) [] expression result) :
    Typing (ShadowSemanticRecords.model Row empty join leRow) [] expression result :=
  (congruenceMap empty join leRow).closed_typing_preserved expression result typed

theorem old_formula_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (formula : Formula α) (assignment : α → Ty Row × Row)
    (held : formula.Holds (StructuralBase.model Row empty join leRow) assignment) :
    formula.Holds (ShadowSemanticRecords.model Row empty join leRow) assignment :=
  (legacyMap empty join leRow).formula_preserved formula assignment held

/-- All original closed typings survive, without excluding any source
constructor or requiring syntactic `IsRecord` evidence about inferred tails. -/
theorem old_closed_typing_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (expression : Expr) (result : Ty Row × Row)
    (typed : Typing (StructuralBase.model Row empty join leRow) [] expression result) :
    Typing (ShadowSemanticRecords.model Row empty join leRow) [] expression result :=
  (legacyMap empty join leRow).closed_typing_preserved expression result typed

/-- Captured environments and explicit signatures keep the same value/row
assignments when only the subtype relation is extended. -/
def mapBinding (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    Binding (StructuralBase.model Row empty join leRow) →
      Binding (ShadowSemanticRecords.model Row empty join leRow)
  | .mono computation => .mono computation
  | .poly expression environment => .poly expression (environment.map (mapBinding empty join leRow))
  | .signature count instantiate => .signature count instantiate

def mapEnvironment (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (environment : List (Binding (StructuralBase.model Row empty join leRow))) :
    List (Binding (ShadowSemanticRecords.model Row empty join leRow)) :=
  environment.map (mapBinding empty join leRow)

/-- Preservation also holds in every open environment, including captured
polymorphic bindings and explicitly quantified signatures. -/
theorem old_typing_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    {environment : List (Binding (StructuralBase.model Row empty join leRow))}
    {expression : Expr} {result : Ty Row × Row}
    (typed : Typing (StructuralBase.model Row empty join leRow) environment expression result) :
    Typing (ShadowSemanticRecords.model Row empty join leRow)
      (mapEnvironment empty join leRow environment) expression result := by
  induction typed using Typing.rec
    (motive_2 := fun binding result _ =>
      BindingTyping (ShadowSemanticRecords.model Row empty join leRow)
        (mapBinding empty join leRow binding) result) with
  | var found _ ih =>
      refine .var ?_ ih
      simp [mapEnvironment, found]
  | lit bounded => exact .lit ((legacyMap empty join leRow).comp_le bounded)
  | lam _ bounded body =>
      exact .lam (by simpa [mapEnvironment, mapBinding] using body)
        ((legacyMap empty join leRow).comp_le bounded)
  | app _ _ bounded function argument =>
      exact .app function argument ((legacyMap empty join leRow).comp_le bounded)
  | letValue value _ _ definition body =>
      exact .letValue value definition (by simpa [mapEnvironment, mapBinding] using body)
  | letComputed _ _ bounded definition body =>
      have adjusted := body
      simp only [mapEnvironment, List.map_cons, mapBinding, Comp.pure] at adjusted
      exact .letComputed definition adjusted
        ((legacyMap empty join leRow).comp_le bounded)
  | branch _ _ _ bounded condition yes no =>
      exact .branch condition yes no ((legacyMap empty join leRow).comp_le bounded)
  | pair _ _ bounded left right =>
      exact .pair left right ((legacyMap empty join leRow).comp_le bounded)
  | fst _ bounded pair => exact .fst pair ((legacyMap empty join leRow).comp_le bounded)
  | snd _ bounded pair => exact .snd pair ((legacyMap empty join leRow).comp_le bounded)
  | emptyRecord bounded => exact .emptyRecord ((legacyMap empty join leRow).comp_le bounded)
  | record _ _ admissible bounded head tail =>
      exact .record head tail (ShadowSemanticRecords.old_subtype admissible)
        ((legacyMap empty join leRow).comp_le bounded)
  | field _ bounded record => exact .field record ((legacyMap empty join leRow).comp_le bounded)
  | variant _ bounded payload => exact .variant payload ((legacyMap empty join leRow).comp_le bounded)
  | mono bounded =>
      rw [mapBinding]
      exact .mono ⟨ShadowSemanticRecords.old_subtype bounded.1, bounded.2⟩
  | poly _ row body =>
      simpa only [mapBinding, mapEnvironment] using BindingTyping.poly body row
  | signature bounded =>
      rw [mapBinding]
      exact .signature ⟨ShadowSemanticRecords.old_subtype bounded.1, bounded.2⟩

theorem singleton_mono {leRow : Row → Row → Prop} (label : Nat) {head head' : Ty Row}
    (bounded : ShadowSemanticRecords.Subtype leRow head head') :
    ShadowSemanticRecords.Subtype leRow (.record label head .emptyRecord) (.record label head' .emptyRecord) := by
  apply ShadowSemanticRecords.Subtype.record (.field .empty) (.field .empty)
  · intro key expected found
    by_cases same : key = label
    · subst key
      exact ⟨head, by simp [StructuralBase.Ty.lookup]⟩
    · simp [StructuralBase.Ty.lookup, same] at found
  · intro key actual expected actualFound expectedFound
    by_cases same : key = label
    · subst key
      simp [StructuralBase.Ty.lookup] at actualFound expectedFound
      subst actual expected
      exact bounded
    · simp [StructuralBase.Ty.lookup, same] at expectedFound

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  ShadowSemanticRecords.model Row algebra.empty algebra.join algebra.le

/-- Every target computation of the original record literal is exactly an
upper instance of its finite singleton-record type. Row antisymmetry and a
syntactic restriction on the inferred tail are not assumptions. -/
theorem literal_typing_iff (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    Typing (model algebra) [] (.record label (.lit base) .emptyRecord) target ↔
      Comp.le (model algebra) (.record label (.base base) .emptyRecord, algebra.empty) target := by
  constructor
  · intro typed
    cases typed with
    | record headTyped tailTyped tailRecord bounded =>
        cases headTyped with
        | lit headBelow =>
            cases tailTyped with
            | emptyRecord tailAbove =>
                have headLift := singleton_mono label headBelow.1
                refine ⟨.trans headLift (.trans ?_ bounded.1), algebra.empty_le _⟩
                exact (ShadowSemanticRecords.record_congr label
                  (ShadowSemanticRecords.Equivalent.refl _) ⟨tailAbove.1, tailRecord⟩).1
  · intro bounded
    apply Typing.record (m := model algebra)
      (a := (Ty.base base, algebra.empty)) (b := (Ty.emptyRecord, algebra.empty))
    · exact .lit ⟨.refl _, algebra.refl _⟩
    · exact .emptyRecord ⟨.refl _, algebra.refl _⟩
    · exact .refl _
    · exact ⟨bounded.1, (algebra.join_le_iff _ _ _).mpr ⟨bounded.2, bounded.2⟩⟩

theorem literal_principal_formula_iff (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    (principal ([] : SchemeEnv Empty) (.record label (.lit base) .emptyRecord)).Holds
        (model algebra) (extend Empty.elim target) ↔
      Comp.le (model algebra) (.record label (.base base) .emptyRecord, algebra.empty) target :=
  (principal_exact (model algebra) _ ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) target).trans
      (literal_typing_iff algebra label base target)

end Yulang.ShadowRecordInference
