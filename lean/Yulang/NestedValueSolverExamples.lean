import Yulang.NestedValueSolver

/-!
# Executed nested subtype saturation

The self-application graph contains actual arrow nodes and a variable bounded
by an arrow containing that same variable. Arrow decomposition and variable
lower/upper propagation meet in its cyclic cache. The rejection examples
reach a rigid contradiction only after decomposing nested constructors.

Accepted examples assert cache consistency, not the unproved general
construction of a recursive principal type from that cache.
-/

namespace Yulang.NestedValueSolverExamples

open StructuralBase NestedValueSolver

def pureRow (_ _ : Unit) : Prop := True
def pureRowCheck (_ _ : Unit) : Bool := true

theorem pureRow_exact (left right : Unit) :
    pureRowCheck left right = true ↔ pureRow left right := by simp [pureRowCheck, pureRow]

/-- The simple-type constraint graph of `(fun x => x) 1`: the identity's
input and result share node 0, while node 1 is the application's result. -/
def identityApplication : Graph 5 Unit := fun node =>
  match node.val with
  | 2 => .base .int
  | 3 => .arrow 0 () 0 ()
  | 4 => .arrow 2 () 1 ()
  | _ => .var

theorem identity_application_propagates_result :
    solve pureRowCheck identityApplication [(3, 4)] =
      some [(2, 1), (2, 0), (0, 1), (3, 4)] := by decide +kernel

/-- A self-application constraint graph sharing one monomorphic function
type. Node 2 is `0 -> 1`, constrained by `0 <= 2` as in `fun x => x x`.
Applying a value of that same type to itself adds `2 <= 2 -> 3`. -/
def selfApplication : Graph 5 Unit := fun node =>
  match node.val with
  | 2 => .arrow 0 () 1 ()
  | 4 => .arrow 2 () 3 ()
  | _ => .var

def selfApplicationConstraints : List (Edge 5) := [(0, 2), (2, 4)]

theorem self_application_cache :
    saturate selfApplication selfApplicationConstraints =
      [(1, 1), (0, 0), (2, 2), (2, 0), (1, 3), (2, 4), (0, 2)] := by decide +kernel

theorem self_application_accepted :
    (solve pureRowCheck selfApplication selfApplicationConstraints).isSome = true := by decide +kernel

theorem self_application_closed :
    Closed selfApplication selfApplicationConstraints
      [(1, 1), (0, 0), (2, 2), (2, 0), (1, 3), (2, 4), (0, 2)] := by
  rw [← self_application_cache]
  exact saturate_closed selfApplication selfApplicationConstraints

/-- `alpha -> str <= int -> str` forces `int <= alpha`. Together with
`alpha <= str`, the variable's lower/upper pair produces `int <= str`. -/
def contravariantConflict : Graph 5 Unit := fun node =>
  match node.val with
  | 0 => .var
  | 1 => .base .int
  | 2 => .base .str
  | 3 => .arrow 0 () 2 ()
  | _ => .arrow 1 () 2 ()

def contravariantConstraints : List (Edge 5) := [(3, 4), (0, 2)]

theorem contravariant_input_propagated :
    (1, 0) ∈ saturate contravariantConflict contravariantConstraints ∧
      (1, 2) ∈ saturate contravariantConflict contravariantConstraints := by decide +kernel

theorem contravariant_conflict_rejected :
    solve pureRowCheck contravariantConflict contravariantConstraints = none := by decide +kernel

theorem contravariant_conflict_has_no_assignment :
    ¬ ∃ value, Models pureRow contravariantConflict contravariantConstraints value :=
  solve_rejects pureRowCheck pureRow (fun _ => True.intro) (fun _ _ => True.intro)
    pureRow_exact contravariantConflict contravariantConstraints contravariant_conflict_rejected

/-- Arrow results contain pairs whose first component remains unknown. -/
def nestedPairConflict : Graph 7 Unit := fun node =>
  match node.val with
  | 0 => .var
  | 1 => .base .int
  | 2 => .base .str
  | 3 => .pair 0 1
  | 4 => .pair 1 2
  | 5 => .arrow 1 () 3 ()
  | _ => .arrow 0 () 4 ()

theorem nested_pair_obligations :
    (3, 4) ∈ saturate nestedPairConflict [(5, 6)] ∧
      (0, 1) ∈ saturate nestedPairConflict [(5, 6)] ∧
      (1, 2) ∈ saturate nestedPairConflict [(5, 6)] := by decide +kernel

theorem nested_pair_conflict_rejected :
    solve pureRowCheck nestedPairConflict [(5, 6)] = none := by decide +kernel

theorem nested_pair_conflict_has_no_assignment :
    ¬ ∃ value, Models pureRow nestedPairConflict [(5, 6)] value :=
  solve_rejects pureRowCheck pureRow (fun _ => True.intro) (fun _ _ => True.intro)
    pureRow_exact nestedPairConflict [(5, 6)] nested_pair_conflict_rejected

/-- The second occurrence of label 7 is hidden by its first occurrence. -/
def recordGraph : Graph 5 Unit := fun node =>
  match node.val with
  | 0 => .base .int
  | 1 => .base .str
  | 2 => .record [(7, 0), (7, 1)]
  | 3 => .record [(7, 0)]
  | _ => .record [(8, 0)]

theorem record_first_field_preserved :
    solve pureRowCheck recordGraph [(2, 3)] = some [(0, 0), (2, 3)] := by decide +kernel

theorem missing_record_field_rejected :
    solve pureRowCheck recordGraph [(2, 4)] = none := by decide +kernel

def variantGraph : Graph 4 Unit := fun node =>
  match node.val with
  | 0 => .base .int
  | 1 => .base .str
  | 2 => .variant 9 0
  | _ => .variant 9 1

theorem variant_payload_rejected :
    solve pureRowCheck variantGraph [(2, 3)] = none := by decide +kernel

/-- Input row obligations reverse together with the input value type. -/
def rowGraph : Graph 3 Nat := fun node =>
  match node.val with
  | 0 => .base .int
  | 1 => .arrow 0 1 0 0
  | _ => .arrow 0 2 0 0

theorem contravariant_row_rejected :
    solve (fun left right : Nat => decide (left ≤ right)) rowGraph [(1, 2)] = none := by decide +kernel

end Yulang.NestedValueSolverExamples
