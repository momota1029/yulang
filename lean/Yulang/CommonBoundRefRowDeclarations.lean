import Yulang.CommonRowDeclarations
import Yulang.CommonBoundRefWorklistRows

/-!
# Total row declaration on actual generated worklist branches

The row declaration computation accepts the original row pairs and all
retained worklist auxiliaries, with no proof or model as an input. Every
actual source or Core clause, and every returned worklist branch over its
pool, is accepted. Successful declaration is exact for every independent
row and type-node assignment.

The success statements concern the result of the finite computation. They
are internal totality lemmas, not restrictions on the parameter families.
-/

namespace Yulang.CommonBoundRefRowDeclarations

open Common (Ty Row)
open PresenceOpenTailGenerationLowering (Pool)
open CommonBoundRefWorklist (Edge Aux State run auxHolds)
open CommonGeneratedPoolRows (AllSimpleRows)
open CommonPresenceConstraintGraph (splitAtoms)
open CommonRowTailInference (RowConstraint RowsHold)
open CommonRowDeclarations (RowPair declareRows declareChecks)
open PresenceSourceConstraintSupport (simpleRow)

variable {m : Nat}

/-- Both finite declarations use only the original syntax and row IDs. -/
def declare (pool : Pool m) (original : List (RowPair m)) (checks : List (Aux pool)) :
    Option (List (RowConstraint m)) :=
  match declareRows original, declareChecks checks with
  | some first, some last => some (first ++ last)
  | _, _ => none

theorem declare_exact (pool : Pool m) (original : List (RowPair m)) (checks : List (Aux pool))
    (declared : List (RowConstraint m)) (success : declare pool original checks = some declared)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    RowsHold declared rows ↔ CommonPresenceConstraintGraph.RowsHold original rows ∧
      ∀ item ∈ checks, auxHolds pool rows values item := by
  cases first : declareRows original with
  | none => simp only [declare, first] at success; cases success
  | some firstDeclared =>
      cases last : declareChecks checks with
      | none => simp only [declare, first, last] at success; cases success
      | some lastDeclared =>
          have same : firstDeclared ++ lastDeclared = declared := by
            simpa only [declare, first, last, Option.some.injEq] using success
          subst declared
          exact (CommonRowDeclarations.rows_hold_append firstDeclared lastDeclared rows).trans
            (and_congr (CommonRowDeclarations.declare_rows_exact original firstDeclared first rows)
              (CommonRowDeclarations.declare_checks_exact checks lastDeclared last rows values
                (CommonSymbolicBoundInspection.BoundRef.eval values)))

theorem row_or_true_iff (pool : Pool m) (item : Aux pool) :
    CommonRowDeclarations.RowOrTrue item ↔ CommonBoundRefWorklist.RowOrTrue item := by
  cases item with
  | flag expression => cases expression <;> rfl
  | _ => rfl

theorem run_declare_checks_some (pool : Pool m) (good : AllSimpleRows pool)
    (edges : List (Edge pool)) (final : State pool) (returned : final ∈ run pool edges) :
    ∃ declared, declareChecks final.aux = some declared :=
  CommonRowDeclarations.declare_checks_some final.aux
    (CommonBoundRefWorklistRows.run_all_rows pool good edges final returned)
    (fun item member => (row_or_true_iff pool item).mpr
      (CommonBoundRefWorklist.run_row_or_true pool edges final returned item member))

theorem run_declare_some (pool : Pool m) (good : AllSimpleRows pool)
    (original : List (RowPair m)) (simple : ∀ pair ∈ original, simpleRow pair.2 = true)
    (edges : List (Edge pool)) (final : State pool) (returned : final ∈ run pool edges) :
    ∃ declared, declare pool original final.aux = some declared := by
  obtain ⟨first, before⟩ := CommonRowDeclarations.declare_rows_some original simple
  obtain ⟨last, after⟩ := run_declare_checks_some pool good edges final returned
  exact ⟨first ++ last, by simp only [declare, before, after]⟩

/-- No shape, support, assignment or row-solver premise is exposed for an
actual source clause. Every returned branch can be declared. -/
theorem generated_run_declare_some (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (edges : List (Edge (splitAtoms clause.pack).pool))
    (final : State (splitAtoms clause.pack).pool)
    (returned : final ∈ run (splitAtoms clause.pack).pool edges) :
    ∃ declared, declare (splitAtoms clause.pack).pool (splitAtoms clause.pack).rows final.aux = some declared :=
  run_declare_some _ (CommonGeneratedPoolRows.generated_pool_rows expression clause member) _
    (CommonRowDeclarations.split_rows_simple clause.pack
      (PresenceSourceConstraintSupport.generated_row_shapes expression clause member))
    edges final returned

theorem generated_core_run_declare_some (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.CoreRules.principalCore
        ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (edges : List (Edge (splitAtoms clause.pack).pool))
    (final : State (splitAtoms clause.pack).pool)
    (returned : final ∈ run (splitAtoms clause.pack).pool edges) :
    ∃ declared, declare (splitAtoms clause.pack).pool (splitAtoms clause.pack).rows final.aux = some declared :=
  run_declare_some _ (CommonGeneratedPoolRows.generated_core_pool_rows expression clause member) _
    (CommonRowDeclarations.split_rows_simple clause.pack
      (CommonPresenceSourceFamily.generated_core_row_shapes expression clause member))
    edges final returned

end Yulang.CommonBoundRefRowDeclarations
