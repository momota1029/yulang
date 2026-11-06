import Yulang.MultiOperationHandlers

/-! Concrete observations separating one multi-operation shallow delimiter
from nesting a delimiter for each operation. Both versions use exactly the
same operation bodies and identity value arms. -/

namespace Yulang.MultiOperationHandlerExamples

open Directed MultiOperationHandlers

def both : Operations Nat 2 := ⟨Fin.val, fun _ _ equal => Fin.eq_of_val_eq equal⟩

def singleton (key : Nat) : Operations Nat 1 :=
  ⟨fun _ => key, fun _ _ _ => Subsingleton.elim _ _⟩

def tailAction : Computation n Nat Unit Unit Nat :=
  .request (raw 1) () (fun _ => .pure 7)

def action : Computation n Nat Unit Unit Nat :=
  .request (raw 0) () (fun _ => tailAction)

def arm (index : Fin 2) (_ : Unit)
    (resume : Unit → Computation n Nat Unit Unit Nat) : Computation n Nat Unit Unit Nat :=
  if index.val = 0 then resume () else .pure 99

def simultaneous : Computation n Nat Unit Unit Nat := handle both Computation.pure arm action

def nested : Computation n Nat Unit Unit Nat :=
  handle (singleton 1) Computation.pure (fun _ _ _ => .pure 99)
    (handle (singleton 0) Computation.pure (fun _ _ resume => resume ()) action)

/-- Capturing operation 0 removes the entire simultaneous handler; operation
1 in its resumption therefore remains observable to the outside. -/
theorem simultaneous_exposes_second : (simultaneous : Computation n Nat Unit Unit Nat) = tailAction := by
  unfold simultaneous action
  have handled := handle_operation (n := n) both Computation.pure arm
    ⟨0, by decide⟩ _ (fun _ => rfl) () (fun _ => tailAction)
  exact handled

/-- In the nested translation, the outer handler is still wrapped around the
inner arm's resumption, so operation 1 is consumed and returns 99. -/
theorem nesting_consumes_second : (nested : Computation n Nat Unit Unit Nat) = .pure 99 := by
  have inner : handle (singleton 0) Computation.pure (fun _ _ resume => resume ())
      (action : Computation n Nat Unit Unit Nat) = tailAction :=
    handle_operation (singleton 0) Computation.pure _ ⟨0, by decide⟩ _ (fun _ => rfl) () _
  unfold nested
  rw [inner]
  exact handle_operation (singleton 1) Computation.pure _ ⟨0, by decide⟩ _ (fun _ => rfl) () _

/-- For every number of signed boundary coordinates, nesting the two
single-operation handlers changes the complete observable request tree. -/
theorem nesting_not_equivalent :
    (simultaneous : Computation n Nat Unit Unit Nat) ≠ nested := by
  rw [simultaneous_exposes_second, nesting_consumes_second]
  intro equal
  cases equal

/-- The same family remains rejected even when another arm is permitted. -/
theorem denied_second_rejected :
    checkPermission (fun key : Nat => key == 0) both = false := by decide

theorem arbitrary_negative_debt_forwarded (debt : Int) (negative : debt < 0)
    (resume : Unit → Computation 1 Nat Unit Unit Nat) :
    handle both Computation.pure arm (.request ⟨1, fun _ => debt⟩ () resume) =
      .request ⟨1, fun _ => debt⟩ ()
        (fun response => handle both Computation.pure arm (resume response)) :=
  handle_nonzero both Computation.pure arm _ () resume ⟨0, by decide⟩ (by change debt ≠ 0; omega)

end Yulang.MultiOperationHandlerExamples
