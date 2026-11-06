import Yulang.SignatureRequests

/-!
# Executable junction handling with ordered multi-shot resumptions

`spec/05-effects.md` §5.9 specifies `or`, `and`, and the abortive `ret`.
`run` implements the library handler: try `true` first, explicitly wrap each
resumed computation again, and try `false` only when required. The equation
`run_is_shallow` connects this recursive library behavior to the actual shallow
handler; it does not change the language's continuation semantics.

Other operations keep their own payload and response types. They and protected
junction occurrences are forwarded with the original signed occurrence.
Every closed well-founded junction condition returns a Boolean. This does not
assert termination of recursive source code or automatic source elaboration.
-/

namespace Yulang.JunctionEffects

open Directed SignatureRequests

/-- These constructors denote `junction::or`, `junction::and`, and
`junction::ret`; external operation identities are retained intact. -/
inductive Operation (External : Type) where
  | disjoin | conjoin | finish
  | external : External → Operation External
  deriving DecidableEq, Repr

def signature (external : Signature External) : Signature (Operation External) where
  Payload
    | .disjoin | .conjoin => Unit
    | .finish => Bool
    | .external operation => external.Payload operation
  Response
    | .disjoin | .conjoin => Bool
    | .finish => Empty
    | .external operation => external.Response operation

def handled : List (Operation External) := [.disjoin, .conjoin, .finish]

variable {External Value : Type} {n : Nat}

/-- The continuation supplied here is explicitly rehandled by the library.
The two calls still originate from the same original multi-shot resumption. -/
def operationBody (external : Signature External) :
    (occurrence : Occurrence n (Operation External)) → Capturable handled occurrence →
    (signature external).Payload occurrence.key →
    ((signature external).Response occurrence.key → Tree n (signature external) Bool) →
      Tree n (signature external) Bool
  | ⟨.disjoin, _⟩, _, _, resume =>
      (resume true).bind (fun first => if first then .pure true else resume false)
  | ⟨.conjoin, _⟩, _, _, resume =>
      (resume true).bind (fun first => if first then resume false else .pure false)
  | ⟨.finish, _⟩, _, result, _ => .pure result
  | ⟨.external _, _⟩, captured, _, _ => False.elim (by
      simp [handled, Capturable] at captured)

def run [DecidableEq External] (external : Signature External) :
    Tree n (signature external) Bool → Tree n (signature external) Bool
  | .pure value => .pure value
  | .request occurrence payload resume =>
      if captured : Capturable handled occurrence then
        operationBody external occurrence captured payload (fun response => run external (resume response))
      else .request occurrence payload (fun response => run external (resume response))

@[simp] theorem run_pure [DecidableEq External] (external : Signature External) (value : Bool) :
    run (n := n) external (.pure value) = .pure value := rfl

theorem run_captured [DecidableEq External] (external : Signature External)
    (occurrence : Occurrence n (Operation External)) (payload : (signature external).Payload occurrence.key)
    (resume : (signature external).Response occurrence.key → Tree n (signature external) Bool)
    (captured : Capturable handled occurrence) :
    run external (.request occurrence payload resume) =
      operationBody external occurrence captured payload (fun response => run external (resume response)) := by
  simp [run, captured]

theorem run_forwarded [DecidableEq External] (external : Signature External)
    (occurrence : Occurrence n (Operation External)) (payload : (signature external).Payload occurrence.key)
    (resume : (signature external).Response occurrence.key → Tree n (signature external) Bool)
    (hidden : ¬ Capturable handled occurrence) :
    run external (.request occurrence payload resume) =
      .request occurrence payload (fun response => run external (resume response)) := by
  simp [run, hidden]

theorem run_nonzero [DecidableEq External] (external : Signature External)
    (occurrence : Occurrence n (Operation External)) (payload : (signature external).Payload occurrence.key)
    (resume : (signature external).Response occurrence.key → Tree n (signature external) Bool)
    (scope : Fin n) (nonzero : occurrence.weights scope ≠ 0) :
    run external (.request occurrence payload resume) =
      .request occurrence payload (fun response => run external (resume response)) :=
  run_forwarded external occurrence payload resume
    (Directed.nonzero_not_capturable handled occurrence scope nonzero)

theorem run_external [DecidableEq External] (external : Signature External) (operation : External)
    (weights : Fin n → Int) (payload : external.Payload operation)
    (resume : external.Response operation → Tree n (signature external) Bool) :
    run external (.request ⟨.external operation, weights⟩ payload resume) =
      .request ⟨.external operation, weights⟩ payload (fun response => run external (resume response)) := by
  simp [run, Capturable, handled]

/-- The recursion is in the library arm. The kernel handler continues to
pass the original, unhandled resumption to that arm. -/
theorem run_is_shallow [DecidableEq External] (external : Signature External)
    (action : Tree n (signature external) Bool) :
    run external action =
      Tree.shallowHandle handled Tree.pure
        (fun occurrence captured payload resume =>
          operationBody external occurrence captured payload
            (fun response => run external (resume response))) action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      by_cases captured : Capturable handled occurrence
      · simp [run, Tree.shallowHandle, captured]
      · simp only [run, Tree.shallowHandle, captured, ↓reduceDIte]
        exact congrArg (Tree.request occurrence payload) (funext ih)

/-- No branch is selected merely to normalize the other branch. -/
theorem run_disjoin [DecidableEq External] (external : Signature External)
    (weights : Fin n → Int) (resume : Bool → Tree n (signature external) Bool)
    (captured : Capturable handled (⟨.disjoin, weights⟩ : Occurrence n (Operation External))) :
    run external (.request ⟨.disjoin, weights⟩ () resume) =
      (run external (resume true)).bind
        (fun first => if first then .pure true else run external (resume false)) := by
  simp [run, captured, operationBody]

theorem run_conjoin [DecidableEq External] (external : Signature External)
    (weights : Fin n → Int) (resume : Bool → Tree n (signature external) Bool)
    (captured : Capturable handled (⟨.conjoin, weights⟩ : Occurrence n (Operation External))) :
    run external (.request ⟨.conjoin, weights⟩ () resume) =
      (run external (resume true)).bind
        (fun first => if first then run external (resume false) else .pure false) := by
  simp [run, captured, operationBody]

theorem run_finish [DecidableEq External] (external : Signature External)
    (weights : Fin n → Int) (value : Bool) (resume : Empty → Tree n (signature external) Bool)
    (captured : Capturable handled (⟨.finish, weights⟩ : Occurrence n (Operation External))) :
    run external (.request ⟨.finish, weights⟩ value resume) = .pure value := by
  simp [run, captured, operationBody]

theorem disjoin_short_circuit [DecidableEq External] (external : Signature External)
    (resume : Bool → Tree n (signature external) Bool)
    (first : run external (resume true) = .pure true) :
    run external (.request (raw .disjoin) () resume) = .pure true := by
  simp [run, Capturable, handled, raw, operationBody, first]

theorem conjoin_short_circuit [DecidableEq External] (external : Signature External)
    (resume : Bool → Tree n (signature external) Bool)
    (first : run external (resume true) = .pure false) :
    run external (.request (raw .conjoin) () resume) = .pure false := by
  simp [run, Capturable, handled, raw, operationBody, first]

theorem disjoin_fallthrough [DecidableEq External] (external : Signature External)
    (resume : Bool → Tree n (signature external) Bool)
    (first : run external (resume true) = .pure false) :
    run external (.request (raw .disjoin) () resume) = run external (resume false) := by
  simp [run, Capturable, handled, raw, operationBody, first]

theorem conjoin_continue [DecidableEq External] (external : Signature External)
    (resume : Bool → Tree n (signature external) Bool)
    (first : run external (resume true) = .pure true) :
    run external (.request (raw .conjoin) () resume) = run external (resume false) := by
  simp [run, Capturable, handled, raw, operationBody, first]

private theorem operationBody_requests (external : Signature External)
    (predicate : Occurrence n (Operation External) → Prop)
    (occurrence : Occurrence n (Operation External)) (captured : Capturable handled occurrence)
    (payload : (signature external).Payload occurrence.key)
    (resume : (signature external).Response occurrence.key → Tree n (signature external) Bool)
    (holds : ∀ response, Tree.AllRequests predicate (resume response)) :
    Tree.AllRequests predicate (operationBody external occurrence captured payload resume) := by
  cases occurrence with
  | mk operation weights =>
      cases operation with
      | disjoin =>
          apply Tree.allRequests_bind _ _ _ (holds true)
          intro first
          cases first
          · exact holds false
          · trivial
      | conjoin =>
          apply Tree.allRequests_bind _ _ _ (holds true)
          intro first
          cases first
          · trivial
          · exact holds false
      | finish => trivial
      | external operation => simp [handled, Capturable] at captured

/-- The helper introduces no request and eliminates every request it can
capture, including ones reached on a second invocation of a continuation. -/
theorem run_requests [DecidableEq External] (external : Signature External)
    (predicate : Occurrence n (Operation External) → Prop) (action : Tree n (signature external) Bool)
    (holds : Tree.AllRequests predicate action) :
    Tree.AllRequests (fun occurrence => predicate occurrence ∧ ¬ Capturable handled occurrence)
      (run external action) := by
  induction action with
  | pure value => trivial
  | request occurrence payload resume ih =>
      by_cases captured : Capturable handled occurrence
      · rw [run_captured _ _ _ _ captured]
        exact operationBody_requests _ _ _ _ _ _ (fun response => ih response (holds.2 response))
      · rw [run_forwarded _ _ _ _ captured]
        exact ⟨⟨holds.1, captured⟩, fun response => ih response (holds.2 response)⟩

theorem run_bounded [DecidableEq External] (external : Signature External)
    (input : Row n (Operation External)) (action : Tree n (signature external) Bool)
    (bound : Tree.BoundedBy input action) :
    Tree.BoundedBy (residual handled input) (run external action) := by
  apply Tree.allRequests_mono _ _ ?_ _ (run_requests external (fun occurrence => occurrence ∈ input) action bound)
  intro occurrence observed
  simpa [residual] using observed

/-- This is a returned Boolean of the actual interpreter, with no supplied
fuel, assumed successful run, or external normalization oracle. -/
theorem closed_returns [DecidableEq External] (external : Signature External)
    (action : Tree n (signature external) Bool)
    (closed : Tree.AllRequests (Capturable handled) action) :
    ∃ result, run external action = .pure result :=
  Tree.no_requests_pure _ (Tree.allRequests_mono _ _
    (fun _ contradiction => contradiction.2 contradiction.1) _ (run_requests external _ action closed))

theorem run_uncaptured [DecidableEq External] (external : Signature External)
    (action : Tree n (signature external) Bool)
    (hidden : Tree.AllRequests (fun occurrence => ¬ Capturable handled occurrence) action) :
    run external action = action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      rw [run_forwarded _ _ _ _ hidden.1]
      exact congrArg (Tree.request occurrence payload)
        (funext (fun response => ih response (hidden.2 response)))

/-! ## Finite `any` and `all` produce the specified quantified conditions -/

def finish (external : Signature External) (result : Bool) : Tree n (signature external) Value :=
  .request (raw .finish) result (fun response => (response : Empty).elim)

def chooseAny (external : Signature External) : List Value → Tree n (signature external) Value
  | [] => finish external false
  | value :: rest => .request (raw .disjoin) ()
      (fun selected : Bool => if selected then .pure value else chooseAny external rest)

def chooseAll (external : Signature External) : List Value → Tree n (signature external) Value
  | [] => finish external true
  | value :: rest => .request (raw .conjoin) ()
      (fun selected : Bool => if selected then .pure value else chooseAll external rest)

theorem run_any_bind [DecidableEq External] (external : Signature External)
    (values : List Value) (continuation : Value → Tree n (signature external) Bool)
    (predicate : Value → Bool) (returns : ∀ value, run external (continuation value) = .pure (predicate value)) :
    run external ((chooseAny external values).bind continuation) = .pure (values.any predicate) := by
  induction values with
  | nil => simp [chooseAny, finish, Tree.bind, run, operationBody, Capturable, handled, raw]
  | cons value rest ih =>
      cases result : predicate value <;>
        simp [chooseAny, Tree.bind, run, operationBody, Capturable, handled, raw, returns, ih, result]

theorem run_all_bind [DecidableEq External] (external : Signature External)
    (values : List Value) (continuation : Value → Tree n (signature external) Bool)
    (predicate : Value → Bool) (returns : ∀ value, run external (continuation value) = .pure (predicate value)) :
    run external ((chooseAll external values).bind continuation) = .pure (values.all predicate) := by
  induction values with
  | nil => simp [chooseAll, finish, Tree.bind, run, operationBody, Capturable, handled, raw]
  | cons value rest ih =>
      cases result : predicate value <;>
        simp [chooseAll, Tree.bind, run, operationBody, Capturable, handled, raw, returns, ih, result]

theorem run_any [DecidableEq External] (external : Signature External)
    (values : List Value) (predicate : Value → Bool) :
    run (n := n) external ((chooseAny external values).map predicate) = .pure (values.any predicate) :=
  run_any_bind external values _ predicate (fun _ => rfl)

theorem run_all [DecidableEq External] (external : Signature External)
    (values : List Value) (predicate : Value → Bool) :
    run (n := n) external ((chooseAll external values).map predicate) = .pure (values.all predicate) :=
  run_all_bind external values _ predicate (fun _ => rfl)

theorem run_all_any [DecidableEq External] {Other : Type} (external : Signature External)
    (left : List Value) (right : List Other) (predicate : Value → Other → Bool) :
    run (n := n) external ((chooseAll external left).bind
        (fun first => (chooseAny external right).map (predicate first))) =
      .pure (left.all (fun first => right.any (predicate first))) :=
  run_all_bind external left _ _ (fun first => run_any external right (predicate first))

end Yulang.JunctionEffects
