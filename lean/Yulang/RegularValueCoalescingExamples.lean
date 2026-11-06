import Yulang.RegularValueCoalescing
import Yulang.NestedValueSolverExamples

/-!
# Executed cyclic inference with constructed principal schemes

These examples upgrade actual successful solver executions to independently
checked regular models and exact instance families. In particular the cyclic
self-application example is no longer merely an accepted cache.
-/

namespace Yulang.RegularValueCoalescingExamples

open RegularValueTypes RegularValueCoalescing
open NestedValueSolverExamples

def selfCache : List (NestedValueSolver.Edge 5) :=
  [(1, 1), (0, 0), (2, 2), (2, 0), (1, 3), (2, 4), (0, 2)]

theorem self_application_solved :
    NestedValueSolver.solve pureRowCheck selfApplication selfApplicationConstraints = some selfCache := by
  decide +kernel

/-- The entire cyclic problem has a solution for every shared parameter
assignment, including assignments whose types are themselves recursive. -/
theorem self_application_all_parameters {State : Type u}
    (parameters : Graph Unit State) (parameter : Fin 5 → Layer Unit State) :
    RegularNestedModels.Models pureRow selfApplication selfApplicationConstraints
      (coalesceGraph selfApplication selfCache parameters parameter) Sum.inl :=
  solve_instantiates_model pureRowCheck pureRow (fun _ _ _ => trivial)
    selfApplication selfApplicationConstraints selfCache self_application_solved parameters parameter

/-- A concrete finite regular witness. None of the original inequalities is
left as an obligation for the free parameters. -/
def selfModel : Graph Unit (Fin 5 ⊕ Unit) :=
  coalesceGraph selfApplication selfCache (fun _ : Unit => Layer.bottom)
    (fun _ => Layer.bottom)

theorem self_application_has_constructed_model :
    RegularNestedModels.Models pureRow selfApplication selfApplicationConstraints selfModel Sum.inl :=
  self_application_all_parameters (fun _ : Unit => Layer.bottom) (fun _ => Layer.bottom)

/-- The application-result node retains every instance of every original
regular solution, rather than only the witness produced above. -/
theorem self_application_principal {State : Type u}
    (targetGraph : Graph Unit State) (target : Layer Unit State) :
    ConstrainedInstance selfApplication selfApplicationConstraints 3 pureRow targetGraph target ↔
      SchemeInstance selfApplication selfCache 3 pureRow targetGraph target :=
  solve_instances_exact pureRowCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureRow_exact selfApplication selfApplicationConstraints selfCache self_application_solved
    3 targetGraph target

def identityCache : List (NestedValueSolver.Edge 5) :=
  [(2, 1), (2, 0), (0, 1), (3, 4)]

theorem identity_application_principal {State : Type u}
    (targetGraph : Graph Unit State) (target : Layer Unit State) :
    ConstrainedInstance identityApplication [(3, 4)] 1 pureRow targetGraph target ↔
      SchemeInstance identityApplication identityCache 1 pureRow targetGraph target :=
  solve_instances_exact pureRowCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureRow_exact identityApplication [(3, 4)] identityCache identity_application_propagates_result
    1 targetGraph target

/-- Recursive assignments cannot repair the contradiction reached only after
reversing an arrow input and propagating its variable bounds. -/
theorem contravariant_conflict_has_no_recursive_model {State : Type u} :
    ¬ ∃ (model : Graph Unit State) (value : Fin 5 → State),
      RegularNestedModels.Models pureRow contravariantConflict contravariantConstraints model value :=
  RegularNestedModels.solve_rejects pureRowCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureRow_exact contravariantConflict contravariantConstraints contravariant_conflict_rejected

/-- Nested arrow-result pairs likewise reject every recursive model. -/
theorem nested_pair_conflict_has_no_recursive_model {State : Type u} :
    ¬ ∃ (model : Graph Unit State) (value : Fin 7 → State),
      RegularNestedModels.Models pureRow nestedPairConflict [(5, 6)] model value :=
  RegularNestedModels.solve_rejects pureRowCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureRow_exact nestedPairConflict [(5, 6)] nested_pair_conflict_rejected

end Yulang.RegularValueCoalescingExamples
