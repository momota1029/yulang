import Yulang.LoopEffects

/-!
# Loop control, retained effects, and finite traversal laws

These laws expose the control behavior of the executable machine. They are
quantified over the original body result type, arbitrary current state and
cursor, signed requests, and external interpreter. `last` and `next` discard
the current body's remainder; `redo` restarts the original body without
restoring an earlier state. The finite-traversal theorem has an explicit
finite traversal derivation, while `redo_forever` has exhausted prefixes of
every length and makes no termination claim.
-/

namespace Yulang.LoopEffects

open Directed SignatureRequests

variable {External Item Cursor State Event Value Result : Type} {n : Nat}
variable {external : Signature External}

def raiseLast (external : Signature External) : Tree n (signature external) Value :=
  .request (raw .last) () Empty.elim

def raiseNext (external : Signature External) : Tree n (signature external) Value :=
  .request (raw .next) () Empty.elim

def raiseRedo (external : Signature External) : Tree n (signature external) Value :=
  .request (raw .redo) () Empty.elim

theorem raiseLast_bind (external : Signature External) (after : Value → Tree n (signature external) Result) :
    (raiseLast external).bind after = raiseLast external := by
  exact congrArg (Tree.request (signature := signature external) (raw .last) ()) (funext (fun impossible => nomatch impossible))

theorem raiseNext_bind (external : Signature External) (after : Value → Tree n (signature external) Result) :
    (raiseNext external).bind after = raiseNext external := by
  exact congrArg (Tree.request (signature := signature external) (raw .next) ()) (funext (fun impossible => nomatch impossible))

theorem raiseRedo_bind (external : Signature External) (after : Value → Tree n (signature external) Result) :
    (raiseRedo external).bind after = raiseRedo external := by
  exact congrArg (Tree.request (signature := signature external) (raw .redo) ()) (funext (fun impossible => nomatch impossible))

/-- Every internal control transition retains the current external state. -/
theorem Step.silent_state {machine : Machine n external Item Cursor State Event Value}
    (transition : Step machine configuration none following) : following.state = configuration.state := by
  cases transition <;> rfl

theorem run_enter [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (cursor rest : Cursor) (item : Item) (fuel : Nat)
    (selected : machine.nextItem cursor = some (item, rest)) :
    machine.run (fuel + 1) ⟨state, .pull cursor⟩ =
      machine.run fuel ⟨state, .body item rest (machine.body item)⟩ := by
  simp [Machine.run, (Step.enter (state := state) selected).executable, Report.prepend]

/-- The body's ordinary value is discarded; it does not become the result
of `for`. The next cursor is used with the unchanged current state. -/
theorem run_body_return [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (item : Item) (rest : Cursor) (value : Value) (fuel : Nat) :
    machine.run (fuel + 1) ⟨state, .body item rest (.pure value)⟩ =
      machine.run fuel ⟨state, .pull rest⟩ := by
  simp [Machine.run, Machine.step, Report.prepend]

/-- Early termination returns unit after two observations, for every old
body resumption and every remaining cursor. Neither is executed. -/
theorem run_last [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (item : Item) (rest : Cursor) (weights : Fin n → Int) (payload : Unit)
    (resume : Empty → Tree n (signature external) Value)
    (visible : Capturable (handled (External := External)) ⟨.last, weights⟩) (fuel : Nat) :
    machine.run (fuel + 2)
      ⟨state, .body item rest (.request ⟨.last, weights⟩ payload resume)⟩ =
        ⟨[], .returned state ()⟩ := by
  simp [Machine.run, Machine.step, visible, Report.prepend]

/-- `next` discards the current remainder and advances to the stored cursor.
No premise about that remainder, next element, or traversal termination occurs. -/
theorem run_next [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (item : Item) (rest : Cursor) (weights : Fin n → Int) (payload : Unit)
    (resume : Empty → Tree n (signature external) Value)
    (visible : Capturable (handled (External := External)) ⟨.next, weights⟩) (fuel : Nat) :
    machine.run (fuel + 1)
      ⟨state, .body item rest (.request ⟨.next, weights⟩ payload resume)⟩ =
        machine.run fuel ⟨state, .pull rest⟩ := by
  simp [Machine.run, Machine.step, visible, Report.prepend]

/-- `redo` restores only the original body, at the same item and cursor.
The state is the state at the request, not the state at iteration entry. -/
theorem run_redo [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (item : Item) (rest : Cursor) (weights : Fin n → Int) (payload : Unit)
    (resume : Empty → Tree n (signature external) Value)
    (visible : Capturable (handled (External := External)) ⟨.redo, weights⟩) (fuel : Nat) :
    machine.run (fuel + 1)
      ⟨state, .body item rest (.request ⟨.redo, weights⟩ payload resume)⟩ =
        machine.run fuel ⟨state, .body item rest (machine.body item)⟩ := by
  simp [Machine.run, Machine.step, visible, Report.prepend]

theorem run_external [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (item : Item) (rest : Cursor) (operation : External) (weights : Fin n → Int)
    (payload : external.Payload operation)
    (resume : external.Response operation → Tree n (signature external) Value)
    (answer : Reply external operation State Event)
    (responded : machine.interpret ⟨operation, weights⟩ payload state = some answer) (fuel : Nat) :
    machine.run (fuel + 1)
      ⟨state, .body item rest (.request ⟨.external operation, weights⟩ payload resume)⟩ =
        (machine.run fuel ⟨answer.state, .body item rest (resume answer.value)⟩).prepend [answer.event] := by
  simp [Machine.run, Machine.step, responded]

/-- A visible redo after an external effect starts the body in the effect's
new state. The external event remains as the first event of the resumed run. -/
theorem external_then_redo [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (item : Item) (rest : Cursor) (operation : External) (weights : Fin n → Int)
    (payload : external.Payload operation)
    (resume : external.Response operation → Tree n (signature external) Value)
    (answer : Reply external operation State Event)
    (responded : machine.interpret ⟨operation, weights⟩ payload state = some answer)
    (restarts : resume answer.value = raiseRedo external) (fuel : Nat) :
    machine.run (fuel + 2)
      ⟨state, .body item rest (.request ⟨.external operation, weights⟩ payload resume)⟩ =
        (machine.run fuel ⟨answer.state, .body item rest (machine.body item)⟩).prepend [answer.event] := by
  rw [run_external machine state item rest operation weights payload resume answer responded,
    restarts]
  have restart := run_redo machine answer.state item rest (fun _ => 0) () Empty.elim
    (by simp [Capturable, handled]) fuel
  exact congrArg (Report.prepend [answer.event]) restart

theorem run_pending [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value)
    (configuration : Configuration n external Item Cursor State Value)
    (pending : Pending machine configuration) (fuel : Nat) :
    machine.run (fuel + 1) configuration = ⟨[], .blocked configuration⟩ := by
  simp [Machine.run, pending.executable]

/-- Finite traversal evidence describes only the caller's cursor protocol.
It does not assume that all possible cursors are finite. -/
inductive Traverses (nextItem : Cursor → Option (Item × Cursor)) : Cursor → List Item → Prop where
  | nil (finished : nextItem cursor = none) : Traverses nextItem cursor []
  | cons (selected : nextItem cursor = some (item, rest))
      (remaining : Traverses nextItem rest items) : Traverses nextItem cursor (item :: items)

/-- Every finite traversal with ordinary, pure bodies returns unit, for
arbitrary body result values and initial external state. The bound is proved
from the traversal length, rather than supplied as an evaluator-success claim. -/
theorem normal_finite_traversal [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (traversal : Traverses machine.nextItem cursor items)
    (normal : ∀ item, item ∈ items → ∃ value, machine.body item = .pure value) :
    machine.run (2 * items.length + 2) ⟨state, .pull cursor⟩ = ⟨[], .returned state ()⟩ := by
  induction traversal with
  | nil finished => simp [Machine.run, Machine.step, finished, Report.prepend]
  | @cons cursor item rest items selected _ ih =>
      obtain ⟨value, completed⟩ := normal item (by simp)
      have budget : 2 * (item :: items).length + 2 = (2 * items.length + 2) + 1 + 1 := by
        simp [List.length_cons, Nat.mul_add, Nat.add_assoc]
      rw [budget, run_enter machine state cursor rest item _ selected, completed, run_body_return]
      exact ih (fun next member => normal next (by simp [member]))

/-- A body consisting of `redo` need not terminate, despite being a finite
request tree. Every finite observation budget ends at the same body and state. -/
theorem redo_forever [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (state : State)
    (item : Item) (rest : Cursor)
    (repeats : machine.body item = raiseRedo external) (fuel : Nat) :
    machine.run fuel ⟨state, .body item rest (raiseRedo external)⟩ =
      ⟨[], .exhausted ⟨state, .body item rest (raiseRedo external)⟩⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      have restart := run_redo machine state item rest (fun _ => 0) () Empty.elim
        (by simp [Capturable, handled]) fuel
      change machine.run (fuel + 1)
        ⟨state, .body item rest (.request ⟨.redo, fun _ => 0⟩ () Empty.elim)⟩ = _
      rw [restart, repeats]
      exact ih

end Yulang.LoopEffects
