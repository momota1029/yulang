import Yulang.SourcePrincipalInference
import Yulang.RecursiveRows

/-!
# Source principal inference over the existing signed set rows

The row carrier is exactly `RecursiveRows.SetRow`: its occurrences retain
scope coordinates, permission information, and unbounded signed balances.
Neither finite support nor a depth bound is imposed on free row parameters.

This specializes the closed core source solver to that existing algebra.
It does not extend `Inference.Expr` with effect operations or claim to solve
arbitrary protect/release/residual `RowExpr` constraints. Those operations
remain available through the unchanged `RowView` below.
-/

namespace Yulang.SignedSourceInference

open Inference

/-- The empty/join/inclusion reduct of the existing signed set-row model. -/
def algebra (scopes : Nat) (Key : Type) : RowFlowSchemes.Algebra (RecursiveRows.SetRow scopes Key) where
  empty := (RecursiveRows.algebra scopes Key).empty
  join := (RecursiveRows.algebra scopes Key).join
  le := (RecursiveRows.algebra scopes Key).le
  refl := fun _ _ member => member
  trans := fun left right occurrence member => right occurrence (left occurrence member)
  empty_le := fun _ _ impossible => False.elim impossible
  join_le_iff := by
    intro left right upper
    constructor
    · intro bounded
      exact ⟨fun occurrence member => bounded occurrence (.inl member),
        fun occurrence member => bounded occurrence (.inr member)⟩
    · rintro ⟨first, last⟩ occurrence (member | member)
      · exact first occurrence member
      · exact last occurrence member

theorem antisymm (scopes : Nat) (Key : Type)
    {left right : RecursiveRows.SetRow scopes Key}
    (forward : (algebra scopes Key).le left right) (backward : (algebra scopes Key).le right left) :
    left = right := by
  funext occurrence
  exact propext ⟨forward occurrence, backward occurrence⟩

def model (scopes : Nat) (Key : Type) : Inference.Model :=
  JointConstraintInference.model (algebra scopes Key)

/-- The solver's model uses the same row meanings as the established
hygiene and operation/handler rules; the decoding map is the identity. -/
def rowView (scopes : Nat) (Key : Type) :
    RowInference.RowView (model scopes Key) (RecursiveRows.algebra scopes Key) where
  decode := id
  decode_empty := rfl
  decode_join := fun _ _ => rfl
  subtype_iff := fun _ _ => Iff.rfl

theorem core_row_evaluation (scopes : Nat) (Key : Type)
    (assignment : α → Comp (model scopes Key)) (term : RowTerm α) :
    (RowInference.fromCoreRow term).eval (RecursiveRows.algebra scopes Key)
        (fun index => (assignment index).2) = term.eval (model scopes Key) assignment :=
  RowInference.eval_fromCoreRow (rowView scopes Key) assignment term

/-- Every original core typing over possibly infinite signed rows is an
instance of the computed family, and every free instance is such a typing. -/
theorem recordFree_instances_exact (scopes : Nat) (Key : Type) (expression : Expr)
    (core : SourceConstraintSupport.RecordFree expression) (target : Comp (model scopes Key)) :
    (SourcePrincipalInference.infer expression).Instance (algebra scopes Key) target ↔
      Typing (model scopes Key) [] expression target :=
  SourcePrincipalInference.recordFree_instances_exact (algebra scopes Key) (antisymm scopes Key)
    expression core target

theorem recordFree_rejected_iff (scopes : Nat) (Key : Type) (expression : Expr)
    (core : SourceConstraintSupport.RecordFree expression) :
    (SourcePrincipalInference.infer expression).status = .rejected ↔
      ¬ ∃ target, Typing (model scopes Key) [] expression target :=
  SourcePrincipalInference.recordFree_rejected_iff (algebra scopes Key) (antisymm scopes Key)
    expression core

theorem recordFree_principal_exact (scopes : Nat) (Key : Type) (expression : Expr)
    (core : SourceConstraintSupport.RecordFree expression) (target : Comp (model scopes Key)) :
    (SourcePrincipalInference.infer expression).Instance (algebra scopes Key) target ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model scopes Key) (extend Empty.elim target) :=
  SourcePrincipalInference.recordFree_principal_formula_exact (algebra scopes Key) (antisymm scopes Key)
    expression core target

end Yulang.SignedSourceInference
