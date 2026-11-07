import Yulang.CommonDemandRoots

/-!
# A partial bound query is not a globally accepted scheme

The first component constrains one variable from below by `int`. The second
component is the independent rigid contradiction `bool <= str`. Querying the
first component returns its exact nonempty lower list, while completing the
actual common solver rejects the whole problem. This records the distinction
needed by a future scheduler: partial bounds may be reported, but they do not
constitute the projection of a globally accepted scheme family.
-/

namespace Yulang.CommonDemandBoundary

open PresenceNormalForm (Atom)
open CommonPresenceConstraintGraph (compile splitAtoms)
open CommonBoundRefWorklist (originalEdges)

def isolatedContradiction : List (Atom (Fin 1)) :=
  [.tyLe (.base .int) (.var 0), .tyLe (.base .bool) (.base .str)]

def requestedLower :=
  CommonDemandSolver.request (splitAtoms isolatedContradiction).pool
    (originalEdges (splitAtoms isolatedContradiction).pool (splitAtoms isolatedContradiction).edges)
    { node := 0, direction := .lower }

theorem requested_lower_nonempty : requestedLower ≠ [] := by decide

/-- Kernel reduction of the real finite solver, without native evaluation. -/
theorem completed_solver_rejects :
    CommonDemandSolver.finishAll (compile isolatedContradiction) = [] := by rfl

theorem reference_solver_rejects :
    CommonBoundRefSolver.solveAll (compile isolatedContradiction) = [] := by
  rw [← CommonDemandSolver.finishAll_exact]
  exact completed_solver_rejects

/-- In particular there is no final scheme instance at any original node,
despite the successful local lower-bound query. -/
theorem no_completed_node_instance
    (node : Fin (compile isolatedContradiction).size) (target : Common.Ty) :
    ¬ ∃ scheme ∈ CommonDemandSolver.finishAll (compile isolatedContradiction),
      ∃ rows : Fin 1 → Common.Row, ∃ parameters : scheme.Parameters,
        Common.Equivalent (scheme.instantiateValues rows parameters node) target := by
  rw [completed_solver_rejects]
  simp only [List.not_mem_nil, false_and, exists_false, not_false_eq_true]

end Yulang.CommonDemandBoundary
