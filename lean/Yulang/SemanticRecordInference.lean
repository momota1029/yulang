import Yulang.SemanticRecords
import Yulang.InferenceModelMap
import Yulang.RowFlowSchemes

/-!
# Preservation of source instances under semantic record congruence

The old type carrier embeds by the identity into the congruence-closed
relation. All constructors, computation rows, source typing rules and
generated formulas stay unchanged. Every old formula model and every old
closed typing therefore survives, including arbitrary record tails and
value-restricted polymorphic lets.

The final theorem characterizes every result of the record literal that
exposed the old boundary. Its ordinary finite record type now represents
all of its typings by subsumption. This is a declarative principal-family
result for that literal, not complete inference for arbitrary source records.
-/

namespace Yulang.SemanticRecordInference

open Inference
open StructuralBase (Ty)

universe u

variable {Row : Type u}

def legacyMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    ModelMap (StructuralBase.model Row empty join leRow) (SemanticRecords.model Row empty join leRow) where
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
  subtype := SemanticRecords.old_subtype
  subrow proof := proof

theorem old_formula_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (formula : Formula α) (assignment : α → Ty Row × Row)
    (held : formula.Holds (StructuralBase.model Row empty join leRow) assignment) :
    formula.Holds (SemanticRecords.model Row empty join leRow) assignment :=
  (legacyMap empty join leRow).formula_preserved formula assignment held

/-- All original closed typings survive, without excluding any source
constructor or requiring syntactic `IsRecord` evidence about inferred tails. -/
theorem old_closed_typing_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (expression : Expr) (result : Ty Row × Row)
    (typed : Typing (StructuralBase.model Row empty join leRow) [] expression result) :
    Typing (SemanticRecords.model Row empty join leRow) [] expression result :=
  (legacyMap empty join leRow).closed_typing_preserved expression result typed

theorem singleton_mono {leRow : Row → Row → Prop} (label : Nat) {head head' : Ty Row}
    (bounded : SemanticRecords.Subtype leRow head head') :
    SemanticRecords.Subtype leRow (.record label head .emptyRecord) (.record label head' .emptyRecord) := by
  apply SemanticRecords.Subtype.record (.field .empty) (.field .empty)
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
  SemanticRecords.model Row algebra.empty algebra.join algebra.le

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
                exact (SemanticRecords.record_congr label
                  (SemanticRecords.Equivalent.refl _) ⟨tailAbove.1, tailRecord⟩).1
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

end Yulang.SemanticRecordInference
