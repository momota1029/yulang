import Std

/-!
# Ordered observations with failure

`Logged` keeps observations made before a computation fails. Its sequencing
operation evaluates the second computation only after the first succeeds.
Combining the returned values never removes observations from either input.

The event type is arbitrary: source-expression visits and future observable
effect events can use the same laws. This module does not introduce effects
into the source AST or assert an operational correspondence for effect handlers.
-/

namespace Yulang.EvaluationTrace

universe u v w x y

structure Logged (Event : Type u) (Error : Type v) (Value : Type w) where
  trace : List Event
  result : Except Error Value
  deriving Repr

namespace Logged

variable {Event : Type u} {Error : Type v} {α : Type w} {β : Type x} {γ : Type y}

def ofResult (result : Except Error α) : Logged Event Error α := ⟨[], result⟩

def prepend (events : List Event) (computation : Logged Event Error α) : Logged Event Error α :=
  ⟨events ++ computation.trace, computation.result⟩

def bind (first : Logged Event Error α) (next : α → Logged Event Error β) : Logged Event Error β :=
  match first.result with
  | .error error => ⟨first.trace, .error error⟩
  | .ok value =>
      let last := next value
      ⟨first.trace ++ last.trace, last.result⟩

/-- The thunk makes the failure boundary explicit even for an executable
caller. The final operation may choose, erase, or combine the returned values. -/
def sequence (first : Logged Event Error α) (second : Unit → Logged Event Error β)
    (finish : α → β → Except Error γ) : Logged Event Error γ :=
  first.bind fun a => (second ()).bind fun b => ofResult (finish a b)

@[simp] theorem prepend_trace (events : List Event) (computation : Logged Event Error α) :
    (computation.prepend events).trace = events ++ computation.trace := rfl

@[simp] theorem prepend_result (events : List Event) (computation : Logged Event Error α) :
    (computation.prepend events).result = computation.result := rfl

@[simp] theorem bind_error (events : List Event) (error : Error)
    (next : α → Logged Event Error β) :
    (Logged.mk events (.error error)).bind next = ⟨events, .error error⟩ := rfl

@[simp] theorem bind_ok (events : List Event) (value : α) (next : α → Logged Event Error β) :
    (Logged.mk events (.ok value)).bind next = ⟨events ++ (next value).trace, (next value).result⟩ := rfl

theorem bind_result (first : Logged Event Error α) (next : α → Logged Event Error β) :
    (first.bind next).result = first.result.bind (fun value => (next value).result) := by
  cases first with
  | mk events result => cases result <;> rfl

@[simp] theorem sequence_first_error (firstTrace : List Event) (error : Error)
    (second : Unit → Logged Event Error β) (finish : α → β → Except Error γ) :
    sequence ⟨firstTrace, .error error⟩ second finish = ⟨firstTrace, .error error⟩ := rfl

@[simp] theorem sequence_second_error (firstTrace lastTrace : List Event) (value : α)
    (error : Error) (finish : α → β → Except Error γ) :
    sequence ⟨firstTrace, .ok value⟩ (fun _ => ⟨lastTrace, .error error⟩) finish =
      ⟨firstTrace ++ lastTrace, .error error⟩ := rfl

/-- Even when the final operation discards one returned value, every event
from its successful evaluation remains in the trace, in written order. -/
@[simp] theorem sequence_values (firstTrace lastTrace : List Event) (first : α) (last : β)
    (finish : α → β → Except Error γ) :
    sequence ⟨firstTrace, .ok first⟩ (fun _ => ⟨lastTrace, .ok last⟩) finish =
      ⟨firstTrace ++ lastTrace, finish first last⟩ := by
  simp [sequence, bind, ofResult]

theorem discarded_second_keeps_observations (firstTrace lastTrace : List Event) (first : α) (last : β) :
    sequence (Error := Error) ⟨firstTrace, .ok first⟩ (fun _ => ⟨lastTrace, .ok last⟩)
      (fun value _ => .ok value) = ⟨firstTrace ++ lastTrace, .ok first⟩ :=
  sequence_values _ _ _ _ _

theorem discarded_first_keeps_observations (firstTrace lastTrace : List Event) (first : α) (last : β) :
    sequence (Error := Error) ⟨firstTrace, .ok first⟩ (fun _ => ⟨lastTrace, .ok last⟩)
      (fun _ value => .ok value) = ⟨firstTrace ++ lastTrace, .ok last⟩ :=
  sequence_values _ _ _ _ _

end Logged

end Yulang.EvaluationTrace
