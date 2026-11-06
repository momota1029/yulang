import Yulang.LoopEffectLaws

/-!
# Executable loop examples with persistent external state

The counter interpreter records every visit and returns its previous value.
The first item restarts once, then advances; the second item stops the loop.
The final trace therefore distinguishes redo from both next and rollback.
Separate examples retain protected requests, finish an unbounded cursor with
`last`, and expose an infinite redo as exhausted at every finite budget.
-/

namespace Yulang.LoopEffectExamples

open Directed SignatureRequests LoopEffects

inductive External where
  | tick | note
  deriving DecidableEq, Repr

def external : Signature External where
  Payload
    | .tick => Nat
    | .note => String
  Response
    | .tick => Nat
    | .note => Unit

inductive Event where
  | tick : Nat → Nat → Nat → Event
  | note : String → Event
  deriving DecidableEq, Repr

abbrev Action := Tree 1 (signature external) Bool
abbrev Config := Configuration 1 external Nat (List Nat) Nat Bool
abbrev LoopReport := Report 1 external Nat (List Nat) Nat Event Bool

def takeItem : List Nat → Option (Nat × List Nat)
  | [] => none
  | item :: rest => some (item, rest)

/-- This concrete interpreter answers only visible external requests. The
generic machine itself merely passes each external occurrence through intact. -/
def interpret : (occurrence : Occurrence 1 External) → external.Payload occurrence.key →
    Nat → Option (Reply external occurrence.key Nat Event)
  | ⟨.tick, weights⟩, item, state =>
      if weights 0 = 0 then some ⟨state, state + 1, .tick item state (state + 1)⟩ else none
  | ⟨.note, weights⟩, message, state =>
      if weights 0 = 0 then some ⟨(), state, .note message⟩ else none

def note (message : String) (after : Action) : Action :=
  .request (raw (.external .note)) message (fun _ => after)

def body (item : Nat) : Action :=
  .request (raw (.external .tick)) item (fun before : Nat =>
    if item = 7 then
      if before = 0 then raiseRedo external
      else (raiseNext external : Tree 1 (signature external) Unit).bind
        (fun _ => note "unreachable after next" (.pure true))
    else (raiseLast external : Tree 1 (signature external) Unit).bind
      (fun _ => note "unreachable after last" (.pure false)))

def machine : Machine 1 external Nat (List Nat) Nat Event Bool where
  nextItem := takeItem
  body := body
  interpret := interpret

def initial : Config := ⟨0, .pull [7, 8, 9]⟩

def afterRedo : Config := ⟨1, .body 7 [8, 9] (body 7)⟩

/-- The prefix ends at the original body for item 7, with the incremented
state and the first visit still recorded. The next item remains 8. -/
theorem redo_keeps_state_and_item :
    machine.run 3 initial = ⟨[.tick 7 0 1], .exhausted afterRedo⟩ := rfl

/-- Item 7 is visited twice, item 8 once, and item 9 never. Neither suffix
after next/last executes. Completion returns unit even though the body type is Bool. -/
theorem redo_next_last :
    machine.run 9 initial =
      ⟨[.tick 7 0 1, .tick 7 1 2, .tick 8 2 3], .returned 3 ()⟩ := rfl

theorem redo_next_last_derivation :
    Prefix machine 9 initial [.tick 7 0 1, .tick 7 1 2, .tick 8 2 3] (.returned 3 ()) :=
  (prefix_iff_run _ _ _ _ _).mpr redo_next_last

theorem resumed_execution :
    (machine.run 6 afterRedo).prepend [.tick 7 0 1] = machine.run 9 initial :=
  (run_add_exhausted machine 3 6 initial afterRedo [.tick 7 0 1] redo_keeps_state_and_item).symm

def protectedRedo : Config :=
  ⟨11, .body 7 [8, 9] (.request (release 0 allowNone (raw .redo)) () Empty.elim)⟩

theorem protected_redo_suspends :
    machine.run 20 protectedRedo = ⟨[], .blocked protectedRedo⟩ := rfl

def protectedExternal : Config :=
  ⟨11, .body 7 [8, 9]
    (.request ⟨.external .tick, fun _ => -1⟩ (7 : Nat) (fun _ => .pure true))⟩

theorem protected_external_suspends :
    machine.run 20 protectedExternal = ⟨[], .blocked protectedExternal⟩ := rfl

def pureMachine (result : Nat → Bool) : Machine 1 external Nat (List Nat) Nat Event Bool :=
  { machine with body := fun item => .pure (result item) }

theorem list_traverses (items : List Nat) : Traverses takeItem items items := by
  induction items with
  | nil => exact .nil rfl
  | cons item rest ih => exact .cons rfl ih

theorem pure_list_returns_unit (result : Nat → Bool) (items : List Nat) (state : Nat) :
    (pureMachine result).run (2 * items.length + 2) ⟨state, .pull items⟩ =
      ⟨[], .returned state ()⟩ :=
  normal_finite_traversal (pureMachine result) state (list_traverses items)
    (fun item _ => ⟨result item, rfl⟩)

/-- This cursor has no end. The finite execution below succeeds because
the body requests last; no termination property of the cursor is assumed. -/
def unbounded : Machine 1 external Nat Nat Nat Event Bool where
  nextItem := fun item => some (item, item + 1)
  body := fun item => if item = 3 then raiseLast external else .pure false
  interpret := interpret

theorem last_exits_unbounded :
    unbounded.run 9 ⟨12, .pull 0⟩ = ⟨[], .returned 12 ()⟩ := rfl

def perpetual : Machine 1 external Nat (List Nat) Nat Event Bool :=
  { machine with body := fun _ => raiseRedo external }

def perpetualStart : Config := ⟨23, .body 7 [8, 9] (raiseRedo external)⟩

theorem perpetual_exhausts_every_budget (fuel : Nat) :
    perpetual.run fuel perpetualStart = ⟨[], .exhausted perpetualStart⟩ :=
  redo_forever perpetual 23 7 [8, 9] rfl fuel

inductive Status where
  | exhausted | blocked | returned
  deriving DecidableEq, Repr

/-- A finite printable observation for the ordinary runner. The kernel
equalities above additionally retain the full suspended configurations. -/
def observe {Cursor : Type} (report : Report 1 external Nat Cursor Nat Event Bool) :
    List Event × Nat × Status :=
  match report.outcome with
  | .exhausted configuration => (report.trace, configuration.state, .exhausted)
  | .blocked configuration => (report.trace, configuration.state, .blocked)
  | .returned state () => (report.trace, state, .returned)

end Yulang.LoopEffectExamples
