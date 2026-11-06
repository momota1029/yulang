import Yulang.RigidRecordQuotient
import Yulang.RigidRecordInference
import Yulang.RecordConstraintSupport
import Yulang.OpenRecordConstraintGraph
import Yulang.SemanticRecordQuotientInference

/-!
# Exact source typing on the semantic quotient

Every quotient computation has a raw representative. The quotient map
preserves all constructors and preserves and reflects both atomic orders.
The original formulas and closed source typings therefore have exactly the
same instances before and after quotienting the congruence-closed model.

This connects the semantic identification required by decisions 38 and 39 to the
original generator, its record literal, and the executable all-core constraint
preparation. The remaining constraint atoms are not claimed to be solved.
-/

namespace Yulang.RigidRecordQuotientInference

open Inference
open StructuralBase (Ty)

universe u

variable {Row : Type u}

def quotientMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row) :
    ModelMap (RigidSemanticRecords.model Row empty join leRow)
      (RigidRecordQuotient.model Row empty join leRow rowRefl) where
  value := RigidRecordQuotient.mk
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
  subtype proof := proof
  subrow proof := proof

theorem computation_surjective (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (target : Comp (RigidRecordQuotient.model Row empty join leRow rowRefl)) :
    ∃ original : Comp (RigidSemanticRecords.model Row empty join leRow),
      (quotientMap empty join leRow rowRefl).comp original = target := by
  rcases target with ⟨value, row⟩
  refine Quotient.inductionOn value ?_
  intro representative
  exact ⟨(representative, row), rfl⟩

/-- Arbitrary free slots, formulas and assignments are covered. Quotient
existential witnesses are reflected using actual representatives. -/
theorem formula_exact (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row) (formula : Formula α) (assignment : α → Ty Row × Row) :
    formula.Holds (RigidRecordQuotient.model Row empty join leRow rowRefl)
        (fun index => (RigidRecordQuotient.mk (assignment index).1, (assignment index).2)) ↔
      formula.Holds (RigidSemanticRecords.model Row empty join leRow) assignment :=
  (quotientMap empty join leRow rowRefl).formula_exact (fun proof => proof) (fun proof => proof)
    (computation_surjective empty join leRow rowRefl) formula assignment

theorem closed_typing_exact (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row) (expression : Expr) (result : Ty Row × Row) :
    Typing (RigidRecordQuotient.model Row empty join leRow rowRefl) [] expression
        (RigidRecordQuotient.mk result.1, result.2) ↔
      Typing (RigidSemanticRecords.model Row empty join leRow) [] expression result :=
  (quotientMap empty join leRow rowRefl).closed_typing_exact (fun proof => proof) (fun proof => proof)
    (computation_surjective empty join leRow rowRefl) expression result

/-- Every old closed typing, including every old record instance, remains
valid after both adding congruence and identifying equivalent value types. -/
theorem old_closed_typing_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row) (expression : Expr) (result : Ty Row × Row)
    (typed : Typing (StructuralBase.model Row empty join leRow) [] expression result) :
    Typing (RigidRecordQuotient.model Row empty join leRow rowRefl) [] expression
      (RigidRecordQuotient.mk result.1, result.2) :=
  (closed_typing_exact empty join leRow rowRefl expression result).mpr
    (RigidRecordInference.old_closed_typing_preserved empty join leRow expression result typed)

/-- Every closed instance already available in the decision-38 quotient
survives. The source expression and result row are unchanged. -/
theorem previous_quotient_typing_preserved (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (expression : Expr)
    (result : Comp (SemanticRecordQuotient.model Row empty join leRow rowRefl))
    (typed : Typing (SemanticRecordQuotient.model Row empty join leRow rowRefl) [] expression result) :
    Typing (RigidRecordQuotient.model Row empty join leRow rowRefl) [] expression
      (RigidRecordQuotient.fromCongruence result.1, result.2) := by
  rcases result with ⟨value, row⟩
  revert typed
  refine Quotient.inductionOn value ?_
  intro representative typed
  apply (closed_typing_exact empty join leRow rowRefl expression (representative, row)).mpr
  exact RigidRecordInference.congruence_closed_typing_preserved empty join leRow expression
    (representative, row)
    ((SemanticRecordQuotientInference.closed_typing_exact empty join leRow rowRefl
      expression (representative, row)).mp typed)

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  RigidRecordQuotient.model Row algebra.empty algebra.join algebra.le algebra.refl

theorem literal_typing_iff (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    Typing (model algebra) [] (.record label (.lit base) .emptyRecord) target ↔
      Comp.le (model algebra)
        (RigidRecordQuotient.mk (.record label (.base base) .emptyRecord), algebra.empty) target := by
  rcases target with ⟨value, row⟩
  refine Quotient.inductionOn value ?_
  intro representative
  exact (closed_typing_exact algebra.empty algebra.join algebra.le algebra.refl _ (representative, row)).trans
    (RigidRecordInference.literal_typing_iff algebra label base (representative, row))

theorem literal_principal_formula_iff (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    (principal ([] : SchemeEnv Empty) (.record label (.lit base) .emptyRecord)).Holds
        (model algebra) (extend Empty.elim target) ↔
      Comp.le (model algebra)
        (RigidRecordQuotient.mk (.record label (.base base) .emptyRecord), algebra.empty) target :=
  (principal_exact (model algebra) _ ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) target).trans
      (literal_typing_iff algebra label base target)

/-- All core expressions, including record construction and both let
alternatives, reach exact prepared constraints over the semantic quotient.
The right side still contains the original problem's model condition. -/
theorem closed_prepared_typing_exact (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (target : Comp (model algebra)) :
    Typing (model algebra) [] expression target ↔
      ∃ clause ∈ ConstraintNormalForm.normalise (principal ([] : SchemeEnv Empty) expression),
        (RecordConstraintSupport.prepare (ConstraintProblems.split clause.pack)).Instance
          (model algebra) (Fin.last clause.locals) target :=
  RecordConstraintSupport.closed_prepared_typing_exact (model algebra)
    RigidRecordQuotient.union_is_join RigidRecordQuotient.le_refl
    (fun {a b c} => RigidRecordQuotient.le_trans a b c) algebra.refl
    (fun first last => algebra.trans first last) expression target

/-- The total source compiler preserves and reflects every closed core
typing on the semantic quotient. This is an exact family of graph models,
not a solved free-parameter principal scheme. -/
theorem compiled_typing_exact (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (target : Comp (model algebra)) :
    OpenRecordConstraintGraph.SourceInstance (model algebra)
        (OpenRecordConstraintGraph.compileSource expression) target ↔
      Typing (model algebra) [] expression target :=
  OpenRecordConstraintGraph.compileSource_instances_exact (model algebra)
    RigidRecordQuotient.union_is_join RigidRecordQuotient.le_refl
    (fun {a b c} => RigidRecordQuotient.le_trans a b c) algebra.refl
    (fun first last => algebra.trans first last) expression target

end Yulang.RigidRecordQuotientInference
