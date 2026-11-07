import Yulang.CommonSignedFreshChoice
import Yulang.CommonSignedUnionCompilation

/-! Actual expression compilation after fresh scope allocation, followed by
literal preimage readback. ALL new scheme parameters are unrestricted; they
need not lie in an old image. Soundness uses expression pullback for arbitrary
new rows; completeness embeds every original independent row model. -/
namespace Yulang.CommonSignedFreshCompilation
open Common (Occurrence Row rowLe)
open CommonEffectRequestGeneration (Permission RowExpr)
open CommonEffectFreshRows (liftOccurrence liftRow)
open CommonEffectFreshExpression (lift lift_join lift_empty lift_rowLe_exact)
open CommonSignedFreshChoice (image pullback pullback_image lift_member)
open CommonSignedExpressionPool (evaluate)
open CommonSignedUnionCompilation (Constraint Problem Models Scheme upperEval)

variable {scopes inputs : Nat}

def rowPullback (row : Row) : Row := fun occurrence => row (liftOccurrence occurrence)

theorem rowPullback_mono (first last : Row) (included : rowLe first last) : rowLe (rowPullback first) (rowPullback last) :=
  fun occurrence member => included (liftOccurrence occurrence) member

theorem transport_pullback (scope : Nat) (permission : Permission) (delta : Int) (row : Row) :
    rowPullback (CommonSignedRows.transport (scope + 1) permission.allows delta row) =
      CommonSignedRows.transport scope permission.allows delta (rowPullback row) := by
  funext occurrence
  change row (CommonSignedRows.shiftOccurrence (scope + 1) permission.allows (-delta) (liftOccurrence occurrence)) =
    row (liftOccurrence (CommonSignedRows.shiftOccurrence scope permission.allows (-delta) occurrence))
  exact congrArg row (CommonEffectFreshRows.lift_shift scope permission (-delta) occurrence).symm

theorem residual_pullback (handled : List Nat) (row : Row) :
    rowPullback (CommonSignedRows.commonResidual handled row) = CommonSignedRows.commonResidual handled (rowPullback row) := by
  funext occurrence
  apply propext
  exact and_congr Iff.rfl (not_congr (CommonEffectFreshExpression.lift_capturable handled occurrence))

theorem head_pullback (scopes key : Nat) :
    rowPullback ((CommonSignedRows.commonAlgebra (scopes + 1)).head key) = (CommonSignedRows.commonAlgebra scopes).head key := by
  rw [← CommonEffectFreshExpression.lift_head]
  funext occurrence
  exact propext (lift_member _ occurrence)

theorem eval_pullback (row : RowExpr scopes (Fin inputs)) (rows : Fin inputs → Row) :
    rowPullback (evaluate rows (lift row)) = evaluate (pullback rows) row := by
  induction row with
  | var | empty => rfl
  | head key => exact head_pullback scopes key
  | union first last iha ihb =>
    change Common.rowJoin (rowPullback (evaluate rows (lift first))) (rowPullback (evaluate rows (lift last))) = _
    exact congr (congrArg Common.rowJoin iha) ihb
  | protect scope permission body ih =>
    exact (transport_pullback scope.val permission 1 (evaluate rows (lift body))).trans
      (congrArg (CommonSignedRows.transport scope.val permission.allows 1) ih)
  | release scope permission body ih =>
    exact (transport_pullback scope.val permission (-1) (evaluate rows (lift body))).trans
      (congrArg (CommonSignedRows.transport scope.val permission.allows (-1)) ih)
  | residual handled body ih =>
    exact (residual_pullback handled (evaluate rows (lift body))).trans
      (congrArg (CommonSignedRows.commonResidual handled) ih)

theorem eval_image (row : RowExpr scopes (Fin inputs)) (rows : Fin inputs → Row) :
    evaluate (image rows) (lift row) = liftRow (evaluate rows row) :=
  CommonEffectFreshExpression.eval_lift row _ _ (fun _ => rfl)

theorem upper_pullback (row : Core.PresenceGeneration.RowTerm (Fin inputs)) (rows : Fin inputs → Row) :
    rowPullback (upperEval rows row) = upperEval (pullback rows) row := by
  induction row with
  | var | empty => rfl
  | join first last iha ihb =>
    change Common.rowJoin (rowPullback (upperEval rows first)) (rowPullback (upperEval rows last)) = _
    exact congr (congrArg Common.rowJoin iha) ihb

theorem upper_image (row : Core.PresenceGeneration.RowTerm (Fin inputs)) (rows : Fin inputs → Row) :
    upperEval (image rows) row = liftRow (upperEval rows row) := by
  induction row with
  | var => rfl
  | empty => exact lift_empty.symm
  | join first last iha ihb =>
    exact (congr (congrArg Common.rowJoin iha) ihb).trans (lift_join (upperEval rows first) (upperEval rows last)).symm

def constraint (original : Constraint scopes inputs) : Constraint (scopes + 1) inputs :=
  ⟨lift original.lower, original.upper⟩

def problem (original : Problem scopes inputs) : Problem (scopes + 1) inputs := original.map constraint

theorem models_pullback (original : Problem scopes inputs) (rows : Fin inputs → Row) (model : Models (problem original) rows) :
    Models original (pullback rows) := by
  intro originalConstraint member
  have accepted := model (constraint originalConstraint) (List.mem_map.mpr ⟨originalConstraint, member, rfl⟩)
  have pulled := rowPullback_mono _ _ accepted
  simpa only [constraint, eval_pullback, upper_pullback] using pulled

theorem models_image_exact (original : Problem scopes inputs) (rows : Fin inputs → Row) :
    Models (problem original) (image rows) ↔ Models original rows := by
  simp only [Models, problem, List.forall_mem_map, constraint, eval_image, upper_image, lift_rowLe_exact]

def solve (original : Problem scopes inputs) : List (Scheme inputs) := CommonSignedUnionCompilation.solve (problem original)

def instantiate (scheme : Scheme inputs) (parameters : Fin scheme.slots → Row) : Fin inputs → Row :=
  pullback (scheme.instantiate parameters)

theorem all_parameters_models (original : Problem scopes inputs) (scheme : Scheme inputs)
    (returned : scheme ∈ solve original) (parameters : Fin scheme.slots → Row) : Models original (instantiate scheme parameters) :=
  models_pullback original _ (CommonSignedUnionCompilation.all_parameters_models (problem original) scheme returned parameters)

/-- Every original row ID is recovered literally. The parameters range over
ALL Common rows in the new carrier, with no image/safety/model condition. -/
theorem solve_all_instances_exact (original : Problem scopes inputs) (rows : Fin inputs → Row) :
    Models original rows ↔ ∃ scheme ∈ solve original, ∃ parameters : Fin scheme.slots → Row, instantiate scheme parameters = rows := by
  constructor
  · intro model
    obtain ⟨scheme, returned, parameters, same⟩ := (CommonSignedUnionCompilation.solve_all_instances_exact (problem original) (image rows)).mp
      ((models_image_exact original rows).mpr model)
    refine ⟨scheme, returned, parameters, ?_⟩
    rw [instantiate, same, pullback_image]
  · rintro ⟨scheme, returned, parameters, same⟩
    rw [← same]
    exact all_parameters_models original scheme returned parameters

end Yulang.CommonSignedFreshCompilation
