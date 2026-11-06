import Yulang.NominalConstructionRuntime
import Yulang.LoopEffects

/-!
# Finite-list observations shared by construction, traversal and indexing

The same ordered `List Value` stored by a nominal list construction supplies
both a traversal cursor and an internal natural-number lookup. `index_exact`
uses an independent position judgement, and `cursor_index` identifies the
next traversed value after any finite number of drops with that lookup.
`loopMachine` installs this cursor in the existing loop evaluator, retaining
its established `last` / `next` / `redo` behavior.

These are views used to implement `Fold` and `Index`; they are not a chosen
source dictionary or a decision about out-of-range/negative integer indexing.
The public `Index` role still needs its integer-key and failure contract.
The source role resolver and method-body elaborator are not replaced here.
-/

namespace Yulang.NominalListViews

open NominalConstructionRuntime NominalConstructions

universe u
variable {Value State : Type u}

/-- The nominal constructor identity stays outside the list contents. -/
def listView (value : Built parameters Value) : Option (List Value) :=
  match value.constructor with
  | .listLiteral _ => some value.values
  | .structLiteral _ | .enumConstructor _ _ => none

@[simp] theorem listView_list (name site : Nat) (types : Fin parameters → ParameterType)
    (values : List Value) :
    listView (⟨.listLiteral name, site, types, values⟩ : Built parameters Value) = some values := rfl

@[simp] theorem listView_struct (name site : Nat) (types : Fin parameters → ParameterType)
    (values : List Value) :
    listView (⟨.structLiteral name, site, types, values⟩ : Built parameters Value) = none := rfl

@[simp] theorem listView_enum (name tag site : Nat) (types : Fin parameters → ParameterType)
    (values : List Value) :
    listView (⟨.enumConstructor name tag, site, types, values⟩ : Built parameters Value) = none := rfl

def nextItem : List Value → Option (Value × List Value)
  | [] => none
  | value :: rest => some (value, rest)

/-- Internal lookup: no surface-language failure policy is encoded by `none`. -/
def index (values : List Value) (position : Nat) : Option Value := values[position]?

inductive At : List Value → Nat → Value → Prop where
  | here {value : Value} {rest : List Value} : At (value :: rest) 0 value
  | there {values : List Value} {position : Nat} {value first : Value} :
      At values position value → At (first :: values) (position + 1) value

theorem index_exact (values : List Value) (position : Nat) (value : Value) :
    index values position = some value ↔ At values position value := by
  induction values generalizing position with
  | nil =>
      constructor
      · simp [index]
      · intro found; cases found
  | cons first rest ih =>
      cases position with
      | zero =>
          constructor
          · intro found
            have same : first = value := Option.some.inj found
            subst value
            exact .here
          · intro found; cases found; rfl
      | succ position =>
          constructor
          · exact fun found => .there ((ih position).mp found)
          · intro found
            cases found with
            | there earlier => exact (ih position).mpr earlier

/-- Traversal and lookup observe the same position and retain the exact suffix. -/
theorem cursor_index (values : List Value) (position : Nat) :
    nextItem (values.drop position) =
      (index values position).map (fun value => (value, values.drop (position + 1))) := by
  induction position generalizing values with
  | zero => cases values <;> rfl
  | succ position ih =>
      cases values with
      | nil => rfl
      | cons value rest => simpa [index] using ih rest

/-- This fold is the finite-list reference body behind a supplied Fold method. -/
def fold (step : State → Value → State) : State → List Value → State
  | initial, [] => initial
  | initial, value :: rest => fold step (step initial value) rest

theorem fold_eq_foldl (step : State → Value → State) (initial : State) (values : List Value) :
    fold step initial values = values.foldl step initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value rest ih => exact ih _

theorem fold_cursor (step : State → Value → State) (initial : State)
    (values : List Value) (value : Value) (rest : List Value)
    (selected : nextItem values = some (value, rest)) :
    fold step initial values = fold step (step initial value) rest := by
  cases values with
  | nil => cases selected
  | cons first tail =>
      have same := Option.some.inj selected
      cases same
      rfl

theorem fold_records_order (values seenBefore : List Value) :
    fold (fun seen value => seen ++ [value]) seenBefore values = seenBefore ++ values := by
  induction values generalizing seenBefore with
  | nil => simp [fold]
  | cons value rest ih => simp [fold, ih, List.append_assoc]

/-- This adapter supplies only the list cursor; loop control and external
interpretation are precisely those of the existing `LoopEffects.Machine`. -/
def loopMachine (external : SignatureRequests.Signature External)
    (body : Item → SignatureRequests.Tree n (LoopEffects.signature external) Result)
    (interpret : (occurrence : Directed.Occurrence n External) → external.Payload occurrence.key →
      Store → Option (LoopEffects.Reply external occurrence.key Store Event)) :
    LoopEffects.Machine n external Item (List Item) Store Event Result where
  nextItem := nextItem
  body := body
  interpret := interpret

theorem loopMachine_enters_head [DecidableEq External]
    (external : SignatureRequests.Signature External)
    (body : Item → SignatureRequests.Tree n (LoopEffects.signature external) Result)
    (interpret : (occurrence : Directed.Occurrence n External) → external.Payload occurrence.key →
      Store → Option (LoopEffects.Reply external occurrence.key Store Event))
    (state : Store) (item : Item) (rest : List Item) :
    (loopMachine external body interpret).step ⟨state, .pull (item :: rest)⟩ =
      .progress none ⟨state, .body item rest (body item)⟩ := rfl

theorem loopMachine_finishes_empty [DecidableEq External]
    (external : SignatureRequests.Signature External)
    (body : Item → SignatureRequests.Tree n (LoopEffects.signature external) Result)
    (interpret : (occurrence : Directed.Occurrence n External) → external.Payload occurrence.key →
      Store → Option (LoopEffects.Reply external occurrence.key Store Event)) (state : Store) :
    (loopMachine external body interpret).step ⟨state, .pull []⟩ =
      .progress none ⟨state, .done⟩ := rfl

end Yulang.NominalListViews
