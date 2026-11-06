import Yulang.NominalListIndex

/-!
# The resolved `index_err: out_of_range int` declaration

Answered Q12 fixes one abortive operation whose payload is the rejected
arbitrary-precision integer. Negative positions, empty lists and positions
past the upper bound use that same operation and retain that same integer.

The local operation family is a disjoint extension of a supplied external
signature. It represents one already resolved declaration; it does not assign
a source nominal identity, choose a module path, look up the strings
`index_err` / `out_of_range`, or select an Index role dictionary. Connecting
those source identities to this family remains an elaboration obligation.
The generic Encoding and Int-to-error APIs are retained unchanged.
-/

namespace Yulang.NominalListIndexError

open Directed SignatureRequests ErrorEffects

inductive Operation (External : Type) where
  | outOfRange
  | external : External → Operation External
  deriving DecidableEq, Repr

inductive Error where
  | outOfRange : Int → Error
  deriving DecidableEq, Repr

def signature (external : Signature External) : Signature (Operation External) where
  Payload
    | .outOfRange => Int
    | .external key => external.Payload key
  Response
    | .outOfRange => Empty
    | .external key => external.Response key

def indexCases (external : Signature External) : Cases (signature external) Error where
  keys := [.outOfRange]
  decode := fun operation declared payload => by
    cases operation with
    | outOfRange => exact .outOfRange payload
    | external key => simp at declared
  noResponse := fun operation declared response => by
    cases operation with
    | outOfRange => exact response
    | external key => simp at declared

def encoding (external : Signature External) : Encoding (indexCases external) where
  operation := fun _ => .outOfRange
  payload := fun error => match error with | .outOfRange position => position
  declared := by intro error; simp [indexCases]
  decoded := by intro error; cases error <;> rfl

theorem encoded_operation (external : Signature External) (position : Int) :
    (encoding external).operation (.outOfRange position) = .outOfRange := rfl

theorem encoded_payload (external : Signature External) (position : Int) :
    (encoding external).payload (.outOfRange position) = position := rfl

theorem encoding_roundtrip (external : Signature External) (error : Error) :
    (indexCases external).decode ((encoding external).operation error) ((encoding external).declared error)
      ((encoding external).payload error) = error := (encoding external).decoded error

/-- Empty responses make the operation abortive without any invented
continuation value or inhabitant of the caller's result type. -/
def abort (external : Signature External) (position : Int) : Tree n (signature external) Value :=
  .request (raw .outOfRange) position (fun response => response.elim)

theorem raise_eq_abort (external : Signature External) (position : Int) :
    raise (n := n) (Value := Value) (encoding external) (.outOfRange position) = abort external position := rfl

def index (external : Signature External) (values : List Value) (position : Int) :
    Tree n (signature external) Value :=
  NominalListViews.effectIndex (encoding external) Error.outOfRange values position

theorem index_returns_iff (external : Signature External) (values : List Value) (position : Int) (value : Value) :
    index (n := n) external values position = .pure value ↔
      ∃ natural, position = Int.ofNat natural ∧ NominalListViews.At values natural value :=
  NominalListViews.effectIndex_returns_iff (encoding external) Error.outOfRange values position value

theorem index_success_iff (external : Signature External) (values : List Value) (position : Int) :
    (∃ value, index (n := n) external values position = .pure value) ↔
      0 ≤ position ∧ position < (values.length : Int) := by
  simp only [index_returns_iff, ← NominalListViews.integerIndex_exact]
  exact NominalListViews.integerIndex_some_iff values position

theorem invalid_index (external : Signature External) (values : List Value) (position : Int)
    (invalid : ¬ NominalListViews.ValidIndex values position) :
    index (n := n) external values position =
      .request (raw .outOfRange) position (fun response => response.elim) :=
  NominalListViews.effectIndex_invalid (encoding external) Error.outOfRange values position invalid

theorem negative_index (external : Signature External) (values : List Value) (position : Int)
    (negative : position < 0) :
    index (n := n) external values position = abort external position := by
  apply invalid_index
  intro valid
  have lower := valid.1
  omega

theorem empty_index (external : Signature External) (position : Int) :
    index (n := n) external ([] : List Value) position = abort external position := by
  apply invalid_index
  intro valid
  have lower := valid.1
  have upper := valid.2
  simp at upper
  omega

theorem upper_index (external : Signature External) (values : List Value) (position : Int)
    (tooLarge : (values.length : Int) ≤ position) :
    index (n := n) external values position = abort external position := by
  apply invalid_index
  intro valid
  have upper := valid.2
  omega

theorem invalid_bind (external : Signature External) (values : List Value) (position : Int)
    (invalid : ¬ NominalListViews.ValidIndex values position)
    (next : Value → Tree n (signature external) Result) :
    (index external values position).bind next = abort external position := by
  change (NominalListViews.effectIndex (encoding external) Error.outOfRange values position).bind next = _
  rw [NominalListViews.effectIndex_invalid _ _ _ _ invalid, raise_bind, raise_eq_abort]

theorem index_bounded (external : Signature External) (values : List Value) (position : Int) :
    Tree.BoundedBy [raw (n := n) (Operation.outOfRange : Operation External)]
      (index external values position) :=
  NominalListViews.effectIndex_bounded (indexCases external) (encoding external) Error.outOfRange values position

theorem wrap_index [DecidableEq External] (external : Signature External) (values : List Value) (position : Int) :
    wrap (n := n) (indexCases external) (index external values position) =
      .pure (match NominalListViews.integerIndex values position with
        | some value => .ok value
        | none => .error (.outOfRange position)) :=
  NominalListViews.wrap_effectIndex (indexCases external) (encoding external) Error.outOfRange values position

theorem wrap_invalid [DecidableEq External] (external : Signature External) (values : List Value) (position : Int)
    (invalid : ¬ NominalListViews.ValidIndex values position) :
    wrap (n := n) (indexCases external) (index external values position) =
      .pure (.error (.outOfRange position)) := by
  rw [wrap_index, (NominalListViews.integerIndex_none_iff values position).mpr invalid]

theorem residual_index_row [DecidableEq External] :
    residual [Operation.outOfRange] [raw (n := n) (Operation.outOfRange : Operation External)] = [] := by
  simp [residual, Capturable, raw]

theorem wrap_index_bounded_empty [DecidableEq External] (external : Signature External)
    (values : List Value) (position : Int) :
    Tree.BoundedBy [] (wrap (n := n) (indexCases external) (index external values position)) := by
  have bound := wrap_bounded (indexCases external) _ _ (index_bounded (n := n) external values position)
  simpa only [indexCases, residual_index_row] using bound

/-- Resolved abortive catch: the selected arm receives the rejected integer,
and executes outside the captured handler. No resumption is supplied. -/
def catchIndex [DecidableEq External] (external : Signature External)
    (onReturn : Value → Tree n (signature external) Result)
    (onOutOfRange : Int → Tree n (signature external) Result)
    (action : Tree n (signature external) Value) : Tree n (signature external) Result :=
  Tree.shallowHandle (indexCases external).keys onReturn
    (fun occurrence captured payload _ =>
      match (indexCases external).decode occurrence.key captured.1 payload with
      | .outOfRange position => onOutOfRange position) action

theorem catch_index [DecidableEq External] (external : Signature External)
    (onReturn : Value → Tree n (signature external) Result)
    (onOutOfRange : Int → Tree n (signature external) Result)
    (values : List Value) (position : Int) :
    catchIndex external onReturn onOutOfRange (index external values position) =
      match NominalListViews.integerIndex values position with
      | some value => onReturn value
      | none => onOutOfRange position := by
  cases found : NominalListViews.integerIndex values position <;>
    simp [catchIndex, index, NominalListViews.effectIndex, found, raise,
      Tree.shallowHandle, indexCases, encoding, Capturable, raw]

theorem catch_invalid [DecidableEq External] (external : Signature External)
    (onReturn : Value → Tree n (signature external) Result)
    (onOutOfRange : Int → Tree n (signature external) Result)
    (values : List Value) (position : Int) (invalid : ¬ NominalListViews.ValidIndex values position) :
    catchIndex external onReturn onOutOfRange (index external values position) = onOutOfRange position := by
  rw [catch_index, (NominalListViews.integerIndex_none_iff values position).mpr invalid]

theorem catch_index_via_wrap [DecidableEq External] (external : Signature External)
    (onReturn : Value → Tree n (signature external) Result)
    (onOutOfRange : Int → Tree n (signature external) Result)
    (values : List Value) (position : Int) :
    catchIndex external onReturn onOutOfRange (index external values position) =
      (wrap (indexCases external) (index external values position)).bind
        (fun result => match result with
          | .ok value => onReturn value
          | .error (.outOfRange rejected) => onOutOfRange rejected) := by
  rw [catch_index, wrap_index]
  cases NominalListViews.integerIndex values position <;> rfl

theorem catch_index_bounded [DecidableEq External] (external : Signature External)
    (onReturn : Value → Tree n (signature external) Result)
    (onOutOfRange : Int → Tree n (signature external) Result) (arms : Row n (Operation External))
    (returnBound : ∀ value, Tree.BoundedBy arms (onReturn value))
    (errorBound : ∀ position, Tree.BoundedBy arms (onOutOfRange position))
    (values : List Value) (position : Int) :
    Tree.BoundedBy arms (catchIndex external onReturn onOutOfRange (index external values position)) := by
  have bound := Tree.shallowHandle_bounded (indexCases external).keys
    [raw (n := n) (Operation.outOfRange : Operation External)] arms onReturn
    (fun occurrence captured payload _ =>
      match (indexCases external).decode occurrence.key captured.1 payload with
      | .outOfRange rejected => onOutOfRange rejected) returnBound
    (fun occurrence captured payload _ _ => by
      cases (indexCases external).decode occurrence.key captured.1 payload with
      | outOfRange rejected => exact errorBound rejected)
    (index external values position) (index_bounded external values position)
  simpa only [indexCases, residual_index_row, List.nil_append, catchIndex] using bound

end Yulang.NominalListIndexError
