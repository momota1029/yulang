import Yulang.Directed

/-!
# Signed requests with operation-specific payloads and responses

The occurrence, signed weights, and capture test are the existing directed
ones. Only the request signature is indexed by its operation. In particular,
an abortive operation can have response type `Empty` while unrelated operations
still return ordinary values. No fake continuation or default return value is
needed for such an operation.

These are well-founded request trees, not a termination claim about recursive
source programs. Constant signatures are isomorphic to `Directed.Computation`,
and their shallow handler agrees with the existing operational handler.
-/

namespace Yulang.SignatureRequests

open Directed

structure Signature (Key : Type) where
  Payload : Key → Type
  Response : Key → Type

inductive Tree {Key : Type} (n : Nat) (signature : Signature Key) (Value : Type) where
  | pure (value : Value)
  | request (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
      (resume : signature.Response occurrence.key → Tree n signature Value)

namespace Tree

variable {Key A B C : Type} {n : Nat} {signature : Signature Key}

def bind (action : Tree n signature A) (next : A → Tree n signature B) : Tree n signature B :=
  match action with
  | .pure value => next value
  | .request occurrence payload resume =>
      .request occurrence payload (fun response => bind (resume response) next)

def map (function : A → B) (action : Tree n signature A) : Tree n signature B :=
  action.bind (fun value => .pure (function value))

@[simp] theorem bind_pure (value : A) (next : A → Tree n signature B) :
    (Tree.pure value).bind next = next value := rfl

@[simp] theorem bind_return (action : Tree n signature A) : action.bind Tree.pure = action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Tree.request occurrence payload) (funext ih)

theorem bind_assoc (action : Tree n signature A) (first : A → Tree n signature B)
    (last : B → Tree n signature C) :
    (action.bind first).bind last = action.bind (fun value => (first value).bind last) := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Tree.request occurrence payload) (funext ih)

theorem bind_eq_pure_iff (action : Tree n signature A) (next : A → Tree n signature B) (result : B) :
    action.bind next = .pure result ↔
      ∃ value, action = .pure value ∧ next value = .pure result := by
  cases action with
  | pure value => simp [bind]
  | request occurrence payload resume => simp [bind]

/-- The arm gets the original resumption. Only forwarding recursively keeps
the handler installed; a captured arm is returned directly. -/
def shallowHandle [DecidableEq Key] (handled : List Key)
    (onReturn : A → Tree n signature B)
    (onOperation : (occurrence : Occurrence n Key) → Capturable handled occurrence →
      signature.Payload occurrence.key →
      (signature.Response occurrence.key → Tree n signature A) → Tree n signature B)
    (action : Tree n signature A) : Tree n signature B :=
  match action with
  | .pure value => onReturn value
  | .request occurrence payload resume =>
      if captured : Capturable handled occurrence then onOperation occurrence captured payload resume
      else .request occurrence payload
        (fun response => shallowHandle handled onReturn onOperation (resume response))

def AllRequests (predicate : Occurrence n Key → Prop) : Tree n signature A → Prop
  | .pure _ => True
  | .request occurrence _ resume => predicate occurrence ∧
      ∀ response, AllRequests predicate (resume response)

def BoundedBy (row : Row n Key) (action : Tree n signature A) : Prop :=
  AllRequests (fun occurrence => occurrence ∈ row) action

theorem allRequests_mono (first last : Occurrence n Key → Prop)
    (implies : ∀ occurrence, first occurrence → last occurrence)
    (action : Tree n signature A) (holds : AllRequests first action) : AllRequests last action := by
  induction action with
  | pure value => trivial
  | request occurrence payload resume ih =>
      exact ⟨implies occurrence holds.1, fun response => ih response (holds.2 response)⟩

theorem allRequests_bind (predicate : Occurrence n Key → Prop)
    (action : Tree n signature A) (next : A → Tree n signature B)
    (first : AllRequests predicate action) (last : ∀ value, AllRequests predicate (next value)) :
    AllRequests predicate (action.bind next) := by
  induction action with
  | pure value => exact last value
  | request occurrence payload resume ih =>
      exact ⟨first.1, fun response => ih response (first.2 response)⟩

theorem no_requests_pure (action : Tree n signature A)
    (none : AllRequests (fun _ => False) action) : ∃ value, action = .pure value := by
  cases action with
  | pure value => exact ⟨value, rfl⟩
  | request occurrence payload resume => exact False.elim none.1

theorem shallowHandle_bounded [DecidableEq Key] (handled : List Key) (input arms : Row n Key)
    (onReturn : A → Tree n signature B)
    (onOperation : (occurrence : Occurrence n Key) → Capturable handled occurrence →
      signature.Payload occurrence.key →
      (signature.Response occurrence.key → Tree n signature A) → Tree n signature B)
    (returnBound : ∀ value, BoundedBy arms (onReturn value))
    (operationBound : ∀ occurrence captured payload resume,
      (∀ response, BoundedBy input (resume response)) →
      BoundedBy arms (onOperation occurrence captured payload resume))
    (action : Tree n signature A) (inputBound : BoundedBy input action) :
    BoundedBy (residual handled input ++ arms)
      (shallowHandle handled onReturn onOperation action) := by
  induction action with
  | pure value =>
      exact allRequests_mono _ _ (fun _ member => List.mem_append.mpr (Or.inr member))
        _ (returnBound value)
  | request occurrence payload resume ih =>
      rcases inputBound with ⟨head, tail⟩
      by_cases captured : Capturable handled occurrence
      · simp only [shallowHandle, captured, ↓reduceDIte]
        exact allRequests_mono _ _ (fun _ member => List.mem_append.mpr (Or.inr member))
          _ (operationBound occurrence captured payload resume tail)
      · simp only [shallowHandle, captured, ↓reduceDIte]
        refine ⟨List.mem_append.mpr (Or.inl ?_), fun response => ih response (tail response)⟩
        simpa [residual, captured] using head

theorem noncapture [DecidableEq Key] (handled : List Key)
    (onReturn : A → Tree n signature B)
    (onOperation : (occurrence : Occurrence n Key) → Capturable handled occurrence →
      signature.Payload occurrence.key →
      (signature.Response occurrence.key → Tree n signature A) → Tree n signature B)
    (action : Tree n signature A)
    (hidden : AllRequests (fun occurrence => ¬ Capturable handled occurrence) action) :
    shallowHandle handled onReturn onOperation action = action.bind onReturn := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      simp only [shallowHandle, hidden.1, ↓reduceDIte, bind]
      exact congrArg (Tree.request occurrence payload)
        (funext (fun response => ih response (hidden.2 response)))

end Tree

/-! ## Exact connection to the existing uniform-signature runtime -/

def Signature.constant (Key Payload Response : Type) : Signature Key :=
  ⟨fun _ => Payload, fun _ => Response⟩

variable {Key Payload Response A B : Type} {n : Nat}

def ofDirected : Computation n Key Payload Response A →
    Tree n (Signature.constant Key Payload Response) A
  | .pure value => .pure value
  | .request occurrence payload resume =>
      .request occurrence payload (fun response => ofDirected (resume response))

def toDirected : Tree n (Signature.constant Key Payload Response) A →
    Computation n Key Payload Response A
  | .pure value => .pure value
  | .request occurrence payload resume =>
      .request occurrence payload (fun response => toDirected (resume response))

@[simp] theorem toDirected_ofDirected (action : Computation n Key Payload Response A) :
    toDirected (ofDirected action) = action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

@[simp] theorem ofDirected_toDirected (action : Tree n (Signature.constant Key Payload Response) A) :
    ofDirected (toDirected action) = action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Tree.request occurrence payload) (funext ih)

/-- This is equality of the actual handlers for all old computations and
arms, not merely preservation of selected examples or effect bounds. -/
theorem ofDirected_shallowHandle [DecidableEq Key] (handled : List Key)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (action : Computation n Key Payload Response A) :
    ofDirected (Computation.shallowHandle handled onReturn onOperation action) =
      Tree.shallowHandle handled (fun value => ofDirected (onReturn value))
        (fun occurrence _ payload resume =>
          ofDirected (onOperation occurrence payload (fun response => toDirected (resume response))))
        (ofDirected action) := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      by_cases captured : Capturable handled occurrence
      · simp [Computation.shallowHandle, Tree.shallowHandle, ofDirected, captured]
      · simp only [Computation.shallowHandle, captured, ↓reduceIte, ofDirected,
          Tree.shallowHandle, ↓reduceDIte]
        exact congrArg (Tree.request (signature := Signature.constant Key Payload Response)
          occurrence payload) (funext ih)

end Yulang.SignatureRequests
