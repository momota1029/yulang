import Yulang.MultiOperationHandlers

/-!
# Partial payload dispatch and the keys a shallow handler may subtract

Q1, answered B in `spec/05-effects.md` 5.2: a permitted operation need not
handle every payload. An unmatched request is forwarded, with its occurrence
and payload unchanged. Only a key with an unguarded irrefutable arm is removed
from the input row. Combining refutable tests does not remove a key.

This is a resolved dispatch layer: a pure payload test is supplied after
pattern elaboration, and an irrefutable pattern is represented explicitly.
Guards here are pure Boolean tests. Effectful defaults/guards, source binding
elaboration and operation-local signatures remain separate obligations. The
same key may occur repeatedly, and dispatch follows the arm order.
-/

namespace Yulang.MultiOperationPayloadHandlers

open Directed MultiOperationHandlers

variable {Key Payload Response A B : Type} {n count : Nat}

inductive PayloadPattern (Payload : Type) where
  | irrefutable
  | test : (Payload → Bool) → PayloadPattern Payload

def PayloadPattern.matches : PayloadPattern Payload → Payload → Bool
  | .irrefutable, _ => true
  | .test check, payload => check payload

structure Arm (Key Payload : Type) where
  key : Key
  pattern : PayloadPattern Payload
  guard : Option (Payload → Bool) := none

def Arm.matches (arm : Arm Key Payload) (payload : Payload) : Bool :=
  arm.pattern.matches payload && (arm.guard.map (fun check => check payload)).getD true

/-- This is a syntactic certificate. Even a guard that always returns true
does not certify subtraction, nor does a union of refutable tests. -/
def Arm.total (arm : Arm Key Payload) : Bool :=
  match arm.pattern, arm.guard with
  | .irrefutable, none => true
  | _, _ => false

theorem Arm.total_iff (arm : Arm Key Payload) :
    arm.total = true ↔ arm.pattern = .irrefutable ∧ arm.guard = none := by
  rcases arm with ⟨key, pattern, guard⟩
  cases pattern <;> cases guard <;> simp [Arm.total]

theorem Arm.total_matches (arm : Arm Key Payload) (total : arm.total = true)
    (payload : Payload) : arm.matches payload = true := by
  rcases arm with ⟨key, pattern, guard⟩
  cases pattern <;> cases guard <;> simp_all [Arm.total, Arm.matches, PayloadPattern.matches]

def keys (arms : Fin count → Arm Key Payload) : List Key :=
  (List.finRange count).map (fun index => (arms index).key)

def removedKeys (arms : Fin count → Arm Key Payload) : List Key :=
  ((List.finRange count).filter (fun index => (arms index).total)).map (fun index => (arms index).key)

@[simp] theorem mem_keys (arms : Fin count → Arm Key Payload) (key : Key) :
    key ∈ keys arms ↔ ∃ index, (arms index).key = key := by
  simp [keys]

@[simp] theorem mem_removedKeys (arms : Fin count → Arm Key Payload) (key : Key) :
    key ∈ removedKeys arms ↔ ∃ index, (arms index).total = true ∧ (arms index).key = key := by
  simp [removedKeys]

def eligible [DecidableEq Key] (arm : Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload) : Bool :=
  decide (Capturable [arm.key] occurrence) && arm.matches payload

@[simp] theorem eligible_exact [DecidableEq Key] (arm : Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload) :
    eligible arm occurrence payload = true ↔
      Capturable [arm.key] occurrence ∧ arm.matches payload = true := by
  simp [eligible]

/-- The first matching arm in written order. No uniqueness of keys is required. -/
def select [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload) : Option (Fin count) :=
  (List.finRange count).find? (fun index => eligible (arms index) occurrence payload)

theorem select_first_iff [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload) (index : Fin count) :
    select arms occurrence payload = some index ↔
      eligible (arms index) occurrence payload = true ∧
      ∃ before after, List.finRange count = before ++ index :: after ∧
        ∀ earlier ∈ before, eligible (arms earlier) occurrence payload = false := by
  simp only [select, List.find?_eq_some_iff_append, Bool.not_eq_true']

theorem select_sound [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload) (index : Fin count)
    (selected : select arms occurrence payload = some index) :
    Capturable [(arms index).key] occurrence ∧ (arms index).matches payload = true :=
  (eligible_exact _ _ _).mp
    (List.find?_some (p := fun candidate => eligible (arms candidate) occurrence payload) selected)

theorem select_none_iff [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload) :
    select arms occurrence payload = none ↔
      ∀ index, eligible (arms index) occurrence payload = false := by
  simp only [select, List.find?_eq_none, List.mem_finRange, forall_const, Bool.not_eq_true]

theorem select_nonzero [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload) (coordinate : Fin n)
    (nonzero : occurrence.weights coordinate ≠ 0) :
    select arms occurrence payload = none := by
  apply (select_none_iff _ _ _).mpr
  intro index
  simp [eligible, nonzero_not_capturable [(arms index).key] occurrence coordinate nonzero]

/-- A missing dispatch cannot have a capturable key certified for subtraction. -/
theorem missed_not_removed [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload)
    (missed : select arms occurrence payload = none) :
    ¬ Capturable (removedKeys arms) occurrence := by
  rintro ⟨member, weights⟩
  obtain ⟨index, total, sameKey⟩ := (mem_removedKeys _ _).mp member
  have accepted : eligible (arms index) occurrence payload = true :=
    (eligible_exact _ _ _).mpr
      ⟨⟨by simp [sameKey], weights⟩, (arms index).total_matches total payload⟩
  have rejected := (select_none_iff _ _ _).mp missed index
  rw [accepted] at rejected
  cases rejected

theorem missed_retained [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (row : Row n Key) (occurrence : Occurrence n Key) (payload : Payload)
    (member : occurrence ∈ row) (missed : select arms occurrence payload = none) :
    occurrence ∈ residual (removedKeys arms) row := by
  simpa [residual, missed_not_removed arms occurrence payload missed] using member

/-- Keys without any unguarded irrefutable arm remain, even when the actual
payload is matched by one of their refutable or guarded arms. -/
theorem partial_key_retained [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (row : Row n Key) (occurrence : Occurrence n Key) (member : occurrence ∈ row)
    (notTotal : ∀ index, (arms index).key = occurrence.key → (arms index).total = false) :
    occurrence ∈ residual (removedKeys arms) row := by
  have notMember : occurrence.key ∉ removedKeys arms := by
    intro present
    obtain ⟨index, total, sameKey⟩ := (mem_removedKeys _ _).mp present
    simp [notTotal index sameKey] at total
  have hidden : ¬ Capturable (removedKeys arms) occurrence := fun h => notMember h.1
  simpa only [residual, List.mem_filter, hidden, decide_false, Bool.not_false, and_true] using member

def handle [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation n Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (action : Computation n Key Payload Response A) : Computation n Key Payload Response B :=
  match action with
  | .pure value => onReturn value
  | .request occurrence payload resume =>
      match select arms occurrence payload with
      | some index => onArm index payload resume
      | none => .request occurrence payload
          (fun response => handle arms onReturn onArm (resume response))

@[simp] theorem handle_pure [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation n Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (value : A) : handle arms onReturn onArm (.pure value) = onReturn value := rfl

/-- The selected arm receives exactly the original resumption (shallow). -/
theorem handle_selected [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation n Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A) (index : Fin count)
    (selected : select arms occurrence payload = some index) :
    handle arms onReturn onArm (.request occurrence payload resume) = onArm index payload resume := by
  simp [handle, selected]

/-- Forwarding preserves the original occurrence and payload. Resuming the
unhandled request continues the still-pending delimiter and value arm. -/
theorem handle_missed [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation n Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A)
    (missed : select arms occurrence payload = none) :
    handle arms onReturn onArm (.request occurrence payload resume) =
      .request occurrence payload (fun response => handle arms onReturn onArm (resume response)) := by
  simp [handle, missed]

theorem handle_multishot [DecidableEq Key] (arms : Fin count → Arm Key Payload)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A) (index : Fin count)
    (selected : select arms occurrence payload = some index) (first last : Response)
    (combine : A → A → Computation n Key Payload Response B)
    (onReturn : A → Computation n Key Payload Response B) :
    handle arms onReturn
      (fun _ _ continuation => (continuation first).bind fun left =>
        (continuation last).bind (combine left))
      (.request occurrence payload resume) =
        (resume first).bind (fun left => (resume last).bind (combine left)) :=
  handle_selected arms onReturn _ occurrence payload resume index selected

/-! ## The previous total table is a special case -/

def ofOperations (operations : Operations Key count) : Fin count → Arm Key Payload :=
  fun index => ⟨operations.key index, .irrefutable, none⟩

@[simp] theorem ofOperations_removedKeys (operations : Operations Key count) :
    removedKeys (ofOperations (Payload := Payload) operations) = operations.keys := by
  simp [removedKeys, ofOperations, Arm.total, Operations.keys, List.finRange,
    List.filter_eq_self.mpr (fun _ _ => rfl), Function.comp_def]

theorem ofOperations_select_captured [DecidableEq Key] (operations : Operations Key count)
    (occurrence : Occurrence n Key) (payload : Payload)
    (captured : Capturable operations.keys occurrence) :
    select (ofOperations operations) occurrence payload =
      some (operations.select occurrence.key captured.1) := by
  cases selected : select (ofOperations operations) occurrence payload with
  | none =>
      have notRemoved := missed_not_removed (ofOperations operations) occurrence payload selected
      simp only [ofOperations_removedKeys] at notRemoved
      exact False.elim (notRemoved captured)
  | some index =>
      have sameKey : operations.key index = occurrence.key := by
        have visible := (select_sound (ofOperations operations) occurrence payload index selected).1.1
        have same : occurrence.key = operations.key index := by simpa [ofOperations] using visible
        exact same.symm
      have equal : index = operations.select occurrence.key captured.1 :=
        operations.distinct (sameKey.trans (operations.select_key _ captured.1).symm)
      simp [equal]

theorem ofOperations_select_missed [DecidableEq Key] (operations : Operations Key count)
    (occurrence : Occurrence n Key) (payload : Payload)
    (hidden : ¬ Capturable operations.keys occurrence) :
    select (ofOperations operations) occurrence payload = none := by
  apply (select_none_iff _ _ _).mpr
  intro index
  have notCaptured : ¬ Capturable [(operations.key index)] occurrence := by
    rintro ⟨member, zero⟩
    apply hidden
    refine ⟨?_, zero⟩
    have sameKey : occurrence.key = operations.key index := by simpa using member
    rw [sameKey]
    exact (operations.mem_keys _).mpr ⟨index, rfl⟩
  simp [eligible, ofOperations, notCaptured]

theorem handle_ofOperations [DecidableEq Key] (operations : Operations Key count)
    (onReturn : A → Computation n Key Payload Response B)
    (onOperation : Fin count → Payload →
      (Response → Computation n Key Payload Response A) → Computation n Key Payload Response B)
    (action : Computation n Key Payload Response A) :
    handle (ofOperations operations) onReturn onOperation action =
      MultiOperationHandlers.handle operations onReturn onOperation action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      by_cases captured : Capturable operations.keys occurrence
      · simp [handle, MultiOperationHandlers.handle, captured,
          ofOperations_select_captured operations occurrence payload captured]
      · simp only [handle, MultiOperationHandlers.handle, captured, ↓reduceDIte,
          ofOperations_select_missed operations occurrence payload captured]
        exact congrArg (Computation.request occurrence payload) (funext ih)

/-! ## Decision 41 still checks every arm, including partial and guarded arms -/

def checkPermission (permission : Permission Key) (arms : Fin count → Arm Key Payload) : Bool :=
  HandlerPermissions.check permission (keys arms)

@[simp] theorem checkPermission_exact (permission : Permission Key)
    (arms : Fin count → Arm Key Payload) :
    checkPermission permission arms = true ↔ ∀ index, permission (arms index).key = true := by
  rw [checkPermission, HandlerPermissions.check_exact]
  constructor
  · intro allowed index
    exact allowed _ ((mem_keys _ _).mpr ⟨index, rfl⟩)
  · intro allowed key member
    obtain ⟨index, rfl⟩ := (mem_keys _ _).mp member
    exact allowed index

theorem checkPermission_rejects (permission : Permission Key)
    (arms : Fin count → Arm Key Payload) (index : Fin count)
    (denied : permission (arms index).key = false) : checkPermission permission arms = false := by
  apply (HandlerPermissions.check_rejects_iff _ _).mpr
  exact ⟨(arms index).key, (mem_keys _ _).mpr ⟨index, rfl⟩, denied⟩

def handleIncoming [DecidableEq Key] (permission : Permission Key) (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A) : Computation (n + 1) Key Payload Response B :=
  handle arms onReturn onArm (HandlerPermissions.enterTree permission action)

def checkedIncoming [DecidableEq Key] (permission : Permission Key) (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A) :
    Except (List Key) (Computation (n + 1) Key Payload Response B) :=
  if checkPermission permission arms then .ok (handleIncoming permission arms onReturn onArm action)
  else .error (HandlerPermissions.diagnostics permission (keys arms))

theorem checkedIncoming_success_iff [DecidableEq Key]
    (permission : Permission Key) (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A)
    (result : Computation (n + 1) Key Payload Response B) :
    checkedIncoming permission arms onReturn onArm action = .ok result ↔
      (∀ index, permission (arms index).key = true) ∧
        handleIncoming permission arms onReturn onArm action = result := by
  cases accepted : checkPermission permission arms <;>
    simp [checkedIncoming, accepted, ← checkPermission_exact]

theorem checkedIncoming_rejected [DecidableEq Key]
    (permission : Permission Key) (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (action : Computation n Key Payload Response A) (index : Fin count)
    (denied : permission (arms index).key = false) :
    checkedIncoming permission arms onReturn onArm action =
      .error (HandlerPermissions.diagnostics permission (keys arms)) := by
  simp [checkedIncoming, checkPermission_rejects permission arms index denied]

theorem incoming_denied_forwarded [DecidableEq Key]
    (permission : Permission Key) (arms : Fin count → Arm Key Payload)
    (onReturn : A → Computation (n + 1) Key Payload Response B)
    (onArm : Fin count → Payload →
      (Response → Computation (n + 1) Key Payload Response A) →
        Computation (n + 1) Key Payload Response B)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response A)
    (denied : permission occurrence.key = false) :
    handleIncoming permission arms onReturn onArm (.request occurrence payload resume) =
      .request (HandlerPermissions.enter permission occurrence) payload
        (fun response => handleIncoming permission arms onReturn onArm (resume response)) := by
  apply handle_missed
  apply (select_none_iff _ _ _).mpr
  intro index
  simp [eligible, HandlerPermissions.denied_never_captured permission [(arms index).key] occurrence denied]

end Yulang.MultiOperationPayloadHandlers
