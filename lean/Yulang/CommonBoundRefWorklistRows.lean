import Yulang.CommonBoundRefWorklist
import Yulang.CommonBoundRefRows
import Yulang.CommonClampedRowFamily

/-!
# Declaring every row auxiliary of the actual finite worklist

Every returned auxiliary check is an original simple-row comparison or the
literal true. Its independent interpretation is therefore exactly the
interpretation of a finite declared row problem. This declaration preserves
the original row identifiers and can be joined to the original row problem.

The resulting row problem feeds the simultaneous clamped family for any
chosen pool with the same input slots. This separates the exact row step
from the remaining proof that all final type edges hold at every parameter.
No semantic condition is stored in the scheme or in its parameters.
-/

namespace Yulang.CommonBoundRefWorklistRows

open Common (Ty Row Equivalent)
open PresenceOpenTailGenerationLowering (Pool)
open CommonGeneratedPoolRows (AllSimpleRows)
open CommonBoundRefWorklist (Edge Aux State RowOrTrue run auxHolds)
open CommonSymbolicBoundInspection (BoundRef)
open CommonSymbolicConstraints (Check Branch)
open CommonSymbolicRowConstraints (AllRows withoutRows declareRows)
open PresenceSourceConstraintSupport (simpleRow)
open CommonRowTailInference (RowConstraint RowsHold)
open CommonPresenceConstraintGraph (Realizes EdgesHold restrict)

variable {m : Nat}

/-- The origin of each retained auxiliary is an actual dispatcher branch.
There is no model, grammar or solver-success premise. -/
theorem run_all_rows (pool : Pool m) (good : AllSimpleRows pool)
    (edges : List (Edge pool)) (final : State pool) (returned : final ∈ run pool edges) :
    AllRows (fun row => simpleRow row = true) final.aux := by
  intro item present
  obtain ⟨edge, branch, included, emitted⟩ :=
    CommonBoundRefWorklist.run_aux_origin pool edges final returned item present
  obtain ⟨original, inspected, contained⟩ :=
    CommonBoundRefWorklist.inspect_aux_origin pool edge branch included item emitted
  exact CommonBoundRefRows.inspect_rows pool good edge.1.val edge.2.val
    original inspected item contained

theorem generated_run_all_rows (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (edges : List (Edge (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool))
    (final : State (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool)
    (returned : final ∈ run (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool edges) :
    AllRows (fun row => simpleRow row = true) final.aux :=
  run_all_rows _ (CommonGeneratedPoolRows.generated_pool_rows expression clause member)
    edges final returned

theorem generated_core_run_all_rows (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.CoreRules.principalCore
        ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (edges : List (Edge (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool))
    (final : State (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool)
    (returned : final ∈ run (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool edges) :
    AllRows (fun row => simpleRow row = true) final.aux :=
  run_all_rows _ (CommonGeneratedPoolRows.generated_core_pool_rows expression clause member)
    edges final returned

theorem without_rows_hold (pool : Pool m) (checks : List (Aux pool))
    (clean : ∀ item ∈ checks, RowOrTrue item)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    Branch.Holds (CommonPresenceConstraintGraph.rowEval rows) values (BoundRef.eval values)
      (withoutRows checks) := by
  induction checks with
  | nil => exact CommonSymbolicConstraints.holds_nil _ _ _
  | cons check rest ih =>
      have head := clean check List.mem_cons_self
      have tail : ∀ item ∈ rest, RowOrTrue item :=
        fun item present => clean item (List.mem_cons_of_mem _ present)
      cases check with
      | childBelow | profileBelow => cases head
      | rowBelow => exact ih tail
      | flag expression =>
          cases expression with
          | literal value =>
              have same : value = true := head
              subst value
              exact (CommonSymbolicConstraints.holds_cons _ _ _ _ _).mpr
                ⟨rfl, ih tail⟩
          | atom | and | or | not => cases head

/-- This equivalence holds for every independent row and node assignment;
constructor equations and type-edge conditions play no part in it. -/
theorem aux_rows_exact (pool : Pool m) (checks : List (Aux pool))
    (good : AllRows (fun row => simpleRow row = true) checks)
    (clean : ∀ item ∈ checks, RowOrTrue item)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    (∀ item ∈ checks, auxHolds pool rows values item) ↔
      RowsHold (declareRows checks good) rows := by
  change Branch.Holds (CommonPresenceConstraintGraph.rowEval rows) values
    (BoundRef.eval values) checks ↔ _
  rw [CommonSymbolicRowConstraints.branch_rows_exact,
    CommonRowTailInference.rows_hold_iff,
    CommonSymbolicRowConstraints.declared_rows_exact]
  exact and_iff_left (without_rows_hold pool checks clean rows values)

def rowConstraints (pool : Pool m) (original : List (RowConstraint m))
    (checks : List (Aux pool)) (good : AllRows (fun row => simpleRow row = true) checks) :
    List (RowConstraint m) := original ++ declareRows checks good

theorem row_constraints_exact (pool : Pool m) (original : List (RowConstraint m))
    (checks : List (Aux pool)) (good : AllRows (fun row => simpleRow row = true) checks)
    (clean : ∀ item ∈ checks, RowOrTrue item)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    RowsHold (rowConstraints pool original checks good) rows ↔
      RowsHold original rows ∧ ∀ item ∈ checks, auxHolds pool rows values item := by
  have split : RowsHold (original ++ declareRows checks good) rows ↔
      RowsHold original rows ∧ RowsHold (declareRows checks good) rows := by
    simp only [RowsHold, List.mem_append, or_imp, forall_and]
  exact split.trans (and_congr Iff.rfl (aux_rows_exact pool checks good clean rows values).symm)

theorem run_row_constraints_exact (pool : Pool m) (good : AllSimpleRows pool)
    (original : List (RowConstraint m)) (edges : List (Edge pool))
    (final : State pool) (returned : final ∈ run pool edges)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    RowsHold (rowConstraints pool original final.aux (run_all_rows pool good edges final returned)) rows ↔
      RowsHold original rows ∧ ∀ item ∈ final.aux, auxHolds pool rows values item :=
  row_constraints_exact pool original final.aux (run_all_rows pool good edges final returned)
    (CommonBoundRefWorklist.run_row_or_true pool edges final returned) rows values

/-- The type pool may be the finite optional extension. It shares exactly
the same row inputs with the original inspected pool. -/
def family (pool valuePool : Pool m) (valueEdges : List (Fin valuePool.size × Fin valuePool.size))
    (original : List (RowConstraint m)) (checks : List (Aux pool))
    (good : AllRows (fun row => simpleRow row = true) checks) : CommonClampedRowFamily.Scheme m :=
  CommonClampedRowFamily.build valuePool valueEdges (rowConstraints pool original checks good)

/-- All final row auxiliaries hold for every row parameter. Their truth is
independent of the node values used to interpret them. -/
theorem family_all_rows (pool valuePool : Pool m)
    (valueEdges : List (Fin valuePool.size × Fin valuePool.size))
    (original : List (RowConstraint m)) (checks : List (Aux pool))
    (good : AllRows (fun row => simpleRow row = true) checks)
    (clean : ∀ item ∈ checks, RowOrTrue item)
    (rowParameters : Fin m → Row) (auxValues : Fin pool.size → Ty) :
    let rows := (family pool valuePool valueEdges original checks good).instantiateRows rowParameters
    RowsHold original rows ∧ ∀ item ∈ checks, auxHolds pool rows auxValues item :=
  (row_constraints_exact pool original checks good clean _ auxValues).mp
    (CommonClampedRowFamily.build_rows_hold valuePool valueEdges _ rowParameters)

theorem run_family_all_rows (pool valuePool : Pool m) (good : AllSimpleRows pool)
    (valueEdges : List (Fin valuePool.size × Fin valuePool.size))
    (original : List (RowConstraint m)) (edges : List (Edge pool))
    (final : State pool) (returned : final ∈ run pool edges)
    (rowParameters : Fin m → Row) (auxValues : Fin pool.size → Ty) :
    let scheme := family pool valuePool valueEdges original final.aux
      (run_all_rows pool good edges final returned)
    let rows := scheme.instantiateRows rowParameters
    RowsHold original rows ∧ ∀ item ∈ final.aux, auxHolds pool rows auxValues item :=
  family_all_rows pool valuePool valueEdges original final.aux
    (run_all_rows pool good edges final returned)
    (CommonBoundRefWorklist.run_row_or_true pool edges final returned) rowParameters auxValues

/-- Any original independent model of the rows, auxiliary rows, constructor
equations and full value-edge list is recovered. The antecedent concerns
that original model, not the free parameters of the constructed family. -/
theorem family_retract (pool valuePool : Pool m)
    (valueEdges : List (Fin valuePool.size × Fin valuePool.size))
    (original : List (RowConstraint m)) (checks : List (Aux pool))
    (good : AllRows (fun row => simpleRow row = true) checks)
    (clean : ∀ item ∈ checks, RowOrTrue item)
    (rows : Fin m → Row) (values : Fin valuePool.size → Ty) (auxValues : Fin pool.size → Ty)
    (rowModel : RowsHold original rows)
    (auxModel : ∀ item ∈ checks, auxHolds pool rows auxValues item)
    (realizes : Realizes valuePool rows values) (valid : EdgesHold valueEdges values) :
    (family pool valuePool valueEdges original checks good).instantiateRows rows = rows ∧
      ∀ slot, Equivalent
        ((family pool valuePool valueEdges original checks good).instantiateValues rows
          (restrict valuePool values, values) slot) (values slot) :=
  CommonClampedRowFamily.build_retract valuePool valueEdges _ rows values
    ((row_constraints_exact pool original checks good clean rows auxValues).mpr ⟨rowModel, auxModel⟩)
    realizes valid

end Yulang.CommonBoundRefWorklistRows
