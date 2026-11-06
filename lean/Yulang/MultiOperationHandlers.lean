import Yulang.HandlerPermissions
import Yulang.OperationalTyping

/-!
# One shallow handler with finitely many resolved operation arms

The table contains one body for each distinct, resolved operation identity and
one value arm. This is a kernel after operation-name and payload-pattern
resolution; it chooses no policy for repeated source clauses of one operation.
The evaluator selects an actual arm by a terminating lookup. A captured arm
gets the original resumption, while forwarding retains this whole handler.

The payload and response carriers here are uniform, as in `OperationalTyping`.
The syntax extension and its independent typing are in
`MultiOperationHandlerTyping`. Operation-local signature polymorphism and
source elaboration remain separate obligations.
-/

namespace Yulang.MultiOperationHandlers

open Directed

variable {Key Payload Response A B : Type} {n count : Nat}

/-- Uniqueness is a kernel representation invariant, not a new source rule. -/
structure Operations (Key : Type) (count : Nat) where
  key : Fin count → Key
  distinct : Function.Injective key

def Operations.keys (operations : Operations Key count) : List Key := List.ofFn operations.key

@[simp] theorem Operations.mem_keys (operations : Operations Key count) (key : Key) :
    key ∈ operations.keys ↔ ∃ index, operations.key index = key := by
  simp [Operations.keys, List.mem_ofFn]

def Operations.locate [DecidableEq Key] (operations : Operations Key count) (key : Key) :
    Option (Fin count) :=
  (List.finRange count).find? (fun index => decide (operations.key index = key))

theorem Operations.locate_sound [DecidableEq Key] (operations : Operations Key count)
    (key : Key) (index : Fin count) (found : operations.locate key = some index) :
    operations.key index = key :=
  of_decide_eq_true (List.find?_some
    (p := fun candidate => decide (operations.key candidate = key)) found)

theorem Operations.locate_none_iff [DecidableEq Key] (operations : Operations Key count)
    (key : Key) : operations.locate key = none ↔ key ∉ operations.keys := by
  simp [Operations.locate, List.find?_eq_none, Operations.mem_keys]

theorem Operations.locate_key [DecidableEq Key] (operations : Operations Key count)
    (index : Fin count) : operations.locate (operations.key index) = some index := by
  cases found : operations.locate (operations.key index) with
  | none =>
      exact False.elim ((operations.locate_none_iff _).mp found
        ((operations.mem_keys _).mpr ⟨index, rfl⟩))
  | some other =>
      have equal := operations.distinct (operations.locate_sound _ _ found)
      cases equal
      rfl

/-- Executable selection from membership, without classical choice. -/
def Operations.select [DecidableEq Key] (operations : Operations Key count)
    (key : Key) (present : key ∈ operations.keys) : Fin count :=
  match found : operations.locate key with
  | some index => index
  | none => False.elim ((operations.locate_none_iff key).mp found present)

theorem Operations.select_key [DecidableEq Key] (operations : Operations Key count)
    (key : Key) (present : key ∈ operations.keys) :
    operations.key (operations.select key present) = key := by
  unfold Operations.select
  split
  · exact operations.locate_sound _ _ ‹_›
  · contradiction

theorem Operations.select_own [DecidableEq Key] (operations : Operations Key count)
    (index : Fin count) (present : operations.key index ∈ operations.keys) :
    operations.select (operations.key index) present = index :=
  operations.distinct (operations.select_key _ present)

/-- All operation arms share one shallow delimiter and one value arm. -/
def handle [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (action : Computation n Key Payload Response A) : Computation n Key Payload Response B :=
  match action with
  | .pure value => onReturn value
  | .request occurrence payload resume =>
      if captured : Capturable operations.keys occurrence then
        onOperation (operations.select occurrence.key captured.1) payload resume
      else .request occurrence payload
        (fun response => handle operations onReturn onOperation (resume response))

@[simp] theorem handle_pure [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (value : A) : handle operations onReturn onOperation (.pure value) = onReturn value := rfl

theorem handle_captured [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A)
    (captured : Capturable operations.keys occurrence) :
    handle operations onReturn onOperation (.request occurrence payload resume) =
      onOperation (operations.select occurrence.key captured.1) payload resume := by
  simp [handle, captured]

/-- Distinct operation identities dispatch to exactly their own arm. -/
theorem handle_operation [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (index : Fin count) (weights : Fin n → Int) (zero : ∀ coordinate, weights coordinate = 0)
    (payload : Payload) (resume : Response → Computation n Key Payload Response A) :
    handle operations onReturn onOperation (.request ⟨operations.key index, weights⟩ payload resume) =
      onOperation index payload resume := by
  have captured : Capturable operations.keys (⟨operations.key index, weights⟩ : Occurrence n Key) :=
    ⟨(operations.mem_keys _).mpr ⟨index, rfl⟩, zero⟩
  rw [handle_captured operations onReturn onOperation _ _ _ captured]
  rw [operations.select_own]

theorem handle_forwarded [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A)
    (hidden : ¬ Capturable operations.keys occurrence) :
    handle operations onReturn onOperation (.request occurrence payload resume) =
      .request occurrence payload
        (fun response => handle operations onReturn onOperation (resume response)) := by
  simp [handle, hidden]

/-- Both positive protection and negative release debt retain every weight. -/
theorem handle_nonzero [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A)
    (coordinate : Fin n) (nonzero : occurrence.weights coordinate ≠ 0) :
    handle operations onReturn onOperation (.request occurrence payload resume) =
      .request occurrence payload
        (fun response => handle operations onReturn onOperation (resume response)) :=
  handle_forwarded operations onReturn onOperation occurrence payload resume
    (nonzero_not_capturable operations.keys occurrence coordinate nonzero)

/-- Resuming twice does not reinstall any operation in the table. -/
theorem handle_multishot [DecidableEq Key] (operations : Operations Key count)
    (index : Fin count) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A) (first last : Response)
    (combine : A → A → Computation n Key Payload Response B)
    (onReturn : A → Computation n Key Payload Response B) :
    handle operations onReturn
      (fun _ _ continuation => (continuation first).bind fun left =>
        (continuation last).bind (combine left))
      (.request (raw (operations.key index)) payload resume) =
        (resume first).bind (fun left => (resume last).bind (combine left)) :=
  handle_operation operations onReturn _ index _ (fun _ => rfl) payload resume

/-- Equality with the existing directed handler when its dispatcher agrees
on declared keys. No assumption is made about undeclared keys. -/
theorem handle_eq_directed [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (dispatcher : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (agree : ∀ index occurrence payload resume, occurrence.key = operations.key index →
      dispatcher occurrence payload resume = onOperation index payload resume)
    (action : Computation n Key Payload Response A) :
    handle operations onReturn onOperation action =
      Computation.shallowHandle operations.keys onReturn dispatcher action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      by_cases captured : Capturable operations.keys occurrence
      · simp only [handle, Computation.shallowHandle, captured, ↓reduceDIte, ↓reduceIte]
        exact (agree _ _ _ _ (operations.select_key occurrence.key captured.1).symm).symm
      · simp only [handle, Computation.shallowHandle, captured, ↓reduceDIte, ↓reduceIte]
        exact congrArg (Computation.request occurrence payload) (funext ih)

/-! ## Incoming-action permission contracts -/

def checkPermission (permission : Permission Key) (operations : Operations Key count) : Bool :=
  HandlerPermissions.check permission operations.keys

@[simp] theorem checkPermission_exact (permission : Permission Key)
    (operations : Operations Key count) :
    checkPermission permission operations = true ↔ ∀ index, permission (operations.key index) = true := by
  rw [checkPermission, HandlerPermissions.check_exact]
  constructor
  · intro permitted index
    exact permitted _ ((operations.mem_keys _).mpr ⟨index, rfl⟩)
  · intro permitted key member
    obtain ⟨index, rfl⟩ := (operations.mem_keys key).mp member
    exact permitted index

theorem checkPermission_rejects [DecidableEq Key] (permission : Permission Key)
    (operations : Operations Key count) (index : Fin count)
    (denied : permission (operations.key index) = false) :
    checkPermission permission operations = false := by
  apply (HandlerPermissions.check_rejects_iff _ _).mpr
  exact ⟨operations.key index, (operations.mem_keys _).mpr ⟨index, rfl⟩, denied⟩

/-- Operation-arm effects remain outside this fresh incoming-action boundary. -/
def handleIncoming [DecidableEq Key] (permission : Permission Key) (operations : Operations Key count)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A) : Computation (n + 1) Key Payload Response B :=
  handle operations onReturn onOperation (HandlerPermissions.enterTree permission action)

def checkedIncoming [DecidableEq Key] (permission : Permission Key) (operations : Operations Key count)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A) :
    Except (List Key) (Computation (n + 1) Key Payload Response B) :=
  if checkPermission permission operations then
    .ok (handleIncoming permission operations onReturn onOperation action)
  else .error (HandlerPermissions.diagnostics permission operations.keys)

theorem checkedIncoming_success_iff [DecidableEq Key]
    (permission : Permission Key) (operations : Operations Key count)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A)
    (result : Computation (n + 1) Key Payload Response B) :
    checkedIncoming permission operations onReturn onOperation action = .ok result ↔
      (∀ index, permission (operations.key index) = true) ∧
        handleIncoming permission operations onReturn onOperation action = result := by
  cases accepted : checkPermission permission operations <;>
    simp [checkedIncoming, accepted, ← checkPermission_exact]

theorem checkedIncoming_rejected [DecidableEq Key]
    (permission : Permission Key) (operations : Operations Key count)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A) (index : Fin count)
    (denied : permission (operations.key index) = false) :
    checkedIncoming permission operations onReturn onOperation action =
      .error (HandlerPermissions.diagnostics permission operations.keys) := by
  simp [checkedIncoming, checkPermission_rejects permission operations index denied]

theorem incoming_denied_forwarded [DecidableEq Key]
    (permission : Permission Key) (operations : Operations Key count)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A)
    (denied : permission occurrence.key = false) :
    handleIncoming permission operations onReturn onOperation (.request occurrence payload resume) =
      .request (HandlerPermissions.enter permission occurrence) payload
        (fun response => handleIncoming permission operations onReturn onOperation (resume response)) := by
  exact handle_forwarded operations onReturn onOperation _ payload _
    (HandlerPermissions.denied_never_captured permission operations.keys occurrence denied)

theorem incoming_allowed_dispatches [DecidableEq Key]
    (permission : Permission Key) (operations : Operations Key count)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (index : Fin count) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A)
    (allowed : permission (operations.key index) = true) :
    handleIncoming permission operations onReturn onOperation
      (.request (raw (operations.key index)) payload resume) =
      onOperation index payload (fun response => HandlerPermissions.enterTree permission (resume response)) := by
  have visible : Capturable operations.keys
      (HandlerPermissions.enter permission (raw (n := n) (operations.key index))) :=
    (HandlerPermissions.enter_raw_capture_iff permission operations.keys _).mpr
      ⟨(operations.mem_keys _).mpr ⟨index, rfl⟩, allowed⟩
  exact handle_operation operations onReturn onOperation index _ visible.2 payload
    (fun response => HandlerPermissions.enterTree permission (resume response))

end Yulang.MultiOperationHandlers
