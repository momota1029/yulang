import Yulang.Inference
import Yulang.RowFlowSchemes
import Yulang.RigidRecordOpaqueBoundary

/-!
# Opaque record alternatives occur in the original closed source judgment

This module connects the union-tail boundary to one unchanged core expression.
Its three record fields, from outermost to innermost, are `x : int`, `x : str`
and `y : int`, with `x = 0`, `y = 1`, and the alternative field `z = 2`.

Typing the `y` literal at `{y:int} | {z:str}` gives a nested opaque result.
Typing the whole inner record at that same union instead gives a flat opaque
result. Both are instances of the same original source expression and its
actual principal formula, for every row join algebra. They are incomparable
in the selected declarative relation, although every rigid record demand
compares with the two results in the same way.

No source program is rejected by this example. It also makes no claim that
a principal scheme or a solver for the full relation cannot exist.
-/

namespace Yulang.RigidRecordSourceBoundary

open Inference
open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordOpaqueBoundary (yField unionTail)

universe u

variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  RigidSemanticRecords.model Row algebra.empty algebra.join algebra.le

def yLiteral : Expr := .record 1 (.lit .int) .emptyRecord
def inner : Expr := .record 0 (.lit .str) yLiteral
def expression : Expr := .record 0 (.lit .int) inner

def nested : Ty Row := .record 0 (.base .int) (.record 0 (.base .str) unionTail)
def flat : Ty Row := .record 0 (.base .int) unionTail

private theorem literal_pure (algebra : RowFlowSchemes.Algebra Row) (base : Base) :
    Typing (model algebra) [] (.lit base) (.base base, algebra.empty) :=
  .lit ⟨.refl _, algebra.refl _⟩

private theorem record_pure (algebra : RowFlowSchemes.Algebra Row) (label : Nat)
    {head tail : Expr} {value rest target : Ty Row}
    (typedHead : Typing (model algebra) [] head (value, algebra.empty))
    (typedTail : Typing (model algebra) [] tail (rest, algebra.empty))
    (admissible : Subtype algebra.le rest .emptyRecord)
    (below : Subtype algebra.le (.record label value rest) target) :
    Typing (model algebra) [] (.record label head tail) (target, algebra.empty) :=
  .record typedHead typedTail admissible
    ⟨below, (algebra.join_le_iff _ _ _).mpr ⟨algebra.refl _, algebra.refl _⟩⟩

theorem y_literal_at (algebra : RowFlowSchemes.Algebra Row) (target : Ty Row)
    (below : Subtype algebra.le yField target) :
    Typing (model algebra) [] yLiteral (target, algebra.empty) :=
  record_pure algebra 1 (literal_pure algebra .int)
    (.emptyRecord ⟨.refl _, algebra.refl _⟩) (.refl _) below

theorem y_literal_union (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] yLiteral (unionTail, algebra.empty) :=
  y_literal_at algebra _ (.unionLeft _ _)

theorem inner_nested (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] inner (.record 0 (.base .str) unionTail, algebra.empty) :=
  record_pure algebra 0 (literal_pure algebra .str) (y_literal_union algebra)
    RigidRecordOpaqueBoundary.union_tail_admissible (.refl _)

theorem inner_union (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] inner (unionTail, algebra.empty) := by
  have forgetX : Subtype algebra.le (.record 0 (.base .str) yField) yField :=
    RigidRecordFields.record_mask_sufficient 0 (.base .str) (.field .empty)
      (RigidRecordFields.erase_subtype 0 (.field .empty))
      (by intro expected found; simp [yField, Ty.lookup] at found)
  exact record_pure algebra 0 (literal_pure algebra .str)
    (y_literal_at algebra _ (.refl _))
    (RigidSemanticRecords.old_subtype (StructuralBase.record_width_to_empty (.field .empty)))
    (.trans forgetX (.unionLeft _ _))

theorem typed_nested (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] expression (nested, algebra.empty) :=
  record_pure algebra 0 (literal_pure algebra .int) (inner_nested algebra)
    (RigidSemanticRecords.record_width 0 (.base .str)
      RigidRecordOpaqueBoundary.union_tail_admissible) (.refl _)

theorem typed_flat (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] expression (flat, algebra.empty) :=
  record_pure algebra 0 (literal_pure algebra .int) (inner_union algebra)
    RigidRecordOpaqueBoundary.union_tail_admissible (.refl _)

theorem result_types_incomparable (leRow : Row → Row → Prop) :
    ¬ Subtype leRow (nested : Ty Row) flat ∧ ¬ Subtype leRow (flat : Ty Row) nested :=
  RigidRecordOpaqueBoundary.union_hidden_incomparable (.base .int) (.base .str)

/-- These are actual instances of a single source expression, not arbitrary
types lying outside the original declaration's instance quantifiers. -/
theorem source_has_incomparable_instances (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] expression (nested, algebra.empty) ∧
      Typing (model algebra) [] expression (flat, algebra.empty) ∧
      ¬ Subtype algebra.le (nested : Ty Row) flat ∧
      ¬ Subtype algebra.le (flat : Ty Row) nested :=
  ⟨typed_nested algebra, typed_flat algebra, result_types_incomparable algebra.le⟩

theorem same_rigid_results (algebra : RowFlowSchemes.Algebra Row) (target : Ty Row)
    (rigid : IsRecord target) (row : Row) :
    Comp.le (model algebra) (nested, algebra.empty) (target, row) ↔
      Comp.le (model algebra) (flat, algebra.empty) (target, row) :=
  and_congr (RigidRecordOpaqueBoundary.hidden_field_rigid_comparison 0
    (.base .int) (.base .str) unionTail rigid) Iff.rfl

private theorem principal_from_typing (algebra : RowFlowSchemes.Algebra Row)
    (target : Comp (model algebra)) (typed : Typing (model algebra) [] expression target) :
    (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  (principal_exact (model algebra) expression ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) target).mpr typed

/-- The unchanged source generator also includes both incomparable output
instances. No success or graph-model premise is supplied to this theorem. -/
theorem principal_has_both_instances (algebra : RowFlowSchemes.Algebra Row) :
    (principal ([] : SchemeEnv Empty) expression).Holds (model algebra)
        (extend Empty.elim (nested, algebra.empty)) ∧
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra)
        (extend Empty.elim (flat, algebra.empty)) :=
  ⟨principal_from_typing algebra _ (typed_nested algebra),
    principal_from_typing algebra _ (typed_flat algebra)⟩

end Yulang.RigidRecordSourceBoundary
