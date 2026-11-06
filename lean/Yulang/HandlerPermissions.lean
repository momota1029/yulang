import Yulang.FreshBoundaries

/-!
# Handler-arm permissions at an incoming computation boundary

Decision 41 checks the arms of a handler for an incoming action against that
action's annotation mask. `check` is executable and `diagnostics` returns
exactly the denied arm keys, in source order. This is a check of the incoming
action's boundary contract, not a global restriction on locally raised effects
or on every handler nested inside a function.

The runtime connection uses the existing signed request trees and allocates a
fresh boundary coordinate. Old positive protection and negative release debt
are retained. This freshness is constructed, not assumed of the caller:
reusing an old coordinate would allow an incoming weight of -1 to cancel +1.

Theorems relate the static diagnostics to actual capture, dispatch, forwarding,
and whole-tree invariance under changing denied arm bodies. The handler applies
the boundary only to its incoming action. Its own arm effects remain outside
that boundary and outside shallow-handler subtraction. No source elaboration,
operation-signature resolution, or whole-language type inference is claimed.
-/

namespace Yulang.HandlerPermissions

open Directed

/-- Allowed arms are retained even when other arms have diagnostics. -/
def permittedArms (permission : Permission Key) (arms : List Key) : List Key :=
  arms.filter permission

/-- One diagnostic per denied source arm; order and repetitions are preserved. -/
def diagnostics (permission : Permission Key) (arms : List Key) : List Key :=
  arms.filter (fun key => !permission key)

/-- The terminating static permission check needs no effect-row solution. -/
def check (permission : Permission Key) (arms : List Key) : Bool :=
  arms.all permission

def Permitted (permission : Permission Key) (arms : List Key) : Prop :=
  ∀ key, key ∈ arms → permission key = true

@[simp] theorem permittedArms_mem (permission : Permission Key) (arms : List Key) (key : Key) :
    key ∈ permittedArms permission arms ↔ key ∈ arms ∧ permission key = true := by
  simp [permittedArms]

@[simp] theorem diagnostics_mem (permission : Permission Key) (arms : List Key) (key : Key) :
    key ∈ diagnostics permission arms ↔ key ∈ arms ∧ permission key = false := by
  simp [diagnostics]

@[simp] theorem check_exact (permission : Permission Key) (arms : List Key) :
    check permission arms = true ↔ Permitted permission arms := by
  simp [check, Permitted]

theorem check_rejects_iff (permission : Permission Key) (arms : List Key) :
    check permission arms = false ↔ ∃ key, key ∈ arms ∧ permission key = false := by
  simp [check, List.all_eq_false]

theorem diagnostics_empty_iff (permission : Permission Key) (arms : List Key) :
    diagnostics permission arms = [] ↔ check permission arms = true := by
  rw [List.eq_nil_iff_forall_not_mem, check_exact]
  simp only [diagnostics_mem, not_and, Bool.not_eq_false, Permitted]

theorem checked_permittedArms (permission : Permission Key) (arms : List Key)
    (accepted : check permission arms = true) : permittedArms permission arms = arms := by
  apply List.filter_eq_self.mpr
  exact (check_exact permission arms).mp accepted

/-- Cross exactly this incoming-action boundary, preserving all old weights. -/
def enter (permission : Permission Key) (occurrence : Occurrence n Key) :
    Occurrence (n + 1) Key :=
  protect FreshBoundaries.fresh permission (FreshBoundaries.liftOccurrence occurrence)

@[simp] theorem enter_key (permission : Permission Key) (occurrence : Occurrence n Key) :
    (enter permission occurrence).key = occurrence.key := rfl

theorem enter_old_weight (permission : Permission Key) (occurrence : Occurrence n Key)
    (coordinate : Fin n) :
    (enter permission occurrence).weights coordinate.succ = occurrence.weights coordinate :=
  FreshBoundaries.fresh_protect_old permission occurrence coordinate

theorem enter_capture_iff (permission : Permission Key) (arms : List Key)
    (occurrence : Occurrence n Key) :
    Capturable arms (enter permission occurrence) ↔
      Capturable arms occurrence ∧ permission occurrence.key = true :=
  FreshBoundaries.fresh_protect_capture_iff arms permission occurrence

theorem enter_raw_capture_iff (permission : Permission Key) (arms : List Key) (key : Key) :
    Capturable arms (enter permission (raw (n := n) key)) ↔
      key ∈ arms ∧ permission key = true := by
  rw [enter_capture_iff]
  simp [Capturable, raw]

/-- Permission is precisely the possibility of catching this incoming key.
The witness for an allowed key is a raw (already-visible) occurrence. -/
theorem permission_iff_capture_possible (permission : Permission Key) (key : Key) :
    permission key = true ↔
      ∃ occurrence : Occurrence n Key, occurrence.key = key ∧
        Capturable [key] (enter permission occurrence) := by
  constructor
  · intro allowed
    exact ⟨raw key, rfl, (enter_raw_capture_iff permission [key] key).mpr
      ⟨List.mem_cons_self, allowed⟩⟩
  · rintro ⟨occurrence, sameKey, captured⟩
    simpa only [sameKey] using ((enter_capture_iff permission [key] occurrence).mp captured).2

/-- A denied key can never be selected, for any old signed weights. -/
theorem denied_never_captured (permission : Permission Key) (arms : List Key)
    (occurrence : Occurrence n Key) (denied : permission occurrence.key = false) :
    ¬ Capturable arms (enter permission occurrence) := by
  intro captured
  have allowed := ((enter_capture_iff permission arms occurrence).mp captured).2
  simp only [denied, Bool.false_eq_true] at allowed

/-- Exact meaning of a static diagnostic: this listed arm is unreachable for
every possible incoming occurrence of its key, not merely for one inferred row. -/
theorem diagnostic_iff_unreachable (permission : Permission Key) (arms : List Key) (key : Key) :
    key ∈ diagnostics permission arms ↔ key ∈ arms ∧
      ∀ occurrence : Occurrence n Key, occurrence.key = key →
        ¬ Capturable arms (enter permission occurrence) := by
  rw [diagnostics_mem]
  constructor
  · rintro ⟨member, denied⟩
    refine ⟨member, fun occurrence sameKey => denied_never_captured permission arms occurrence ?_⟩
    simpa only [sameKey] using denied
  · rintro ⟨member, unreachable⟩
    refine ⟨member, ?_⟩
    cases allowed : permission key with
    | false => rfl
    | true => exact False.elim (unreachable (raw key) rfl
        ((enter_raw_capture_iff permission arms key).mpr ⟨member, allowed⟩))

/-- Permission cannot remove pre-existing positive protection or negative debt. -/
theorem old_nonzero_blocks (permission : Permission Key) (arms : List Key)
    (occurrence : Occurrence n Key) (coordinate : Fin n)
    (nonzero : occurrence.weights coordinate ≠ 0) :
    ¬ Capturable arms (enter permission occurrence) := by
  intro captured
  exact nonzero (((enter_capture_iff permission arms occurrence).mp captured).1.2 coordinate)

theorem capture_after_check (permission : Permission Key) (arms : List Key)
    (accepted : check permission arms = true) (occurrence : Occurrence n Key) :
    Capturable arms (enter permission occurrence) ↔ Capturable arms occurrence := by
  rw [enter_capture_iff]
  exact ⟨And.left, fun captured =>
    ⟨captured, (check_exact permission arms).mp accepted occurrence.key captured.1⟩⟩

theorem capture_permittedArms_iff (permission : Permission Key) (arms : List Key)
    (occurrence : Occurrence n Key) :
    Capturable arms (enter permission occurrence) ↔
      Capturable (permittedArms permission arms) (enter permission occurrence) := by
  rw [enter_capture_iff, enter_capture_iff]
  simp only [Capturable, permittedArms_mem]
  exact ⟨fun ⟨⟨member, zero⟩, allowed⟩ => ⟨⟨⟨member, allowed⟩, zero⟩, allowed⟩,
    fun ⟨⟨⟨member, _⟩, zero⟩, allowed⟩ => ⟨⟨member, zero⟩, allowed⟩⟩

/-- Row subtraction uses exactly the same selective permission as dispatch. -/
theorem residual_incoming [DecidableEq Key] (permission : Permission Key)
    (arms : List Key) (row : Row n Key) :
    residual arms (row.map (enter permission)) =
      (residual (permittedArms permission arms) row).map (enter permission) :=
  FreshBoundaries.fresh_protect_residual arms permission row

theorem checked_residual_incoming [DecidableEq Key] (permission : Permission Key)
    (arms : List Key) (accepted : check permission arms = true) (row : Row n Key) :
    residual arms (row.map (enter permission)) =
      (residual arms row).map (enter permission) := by
  rw [residual_incoming, checked_permittedArms permission arms accepted]

/-- Transport the complete incoming request tree; arm outputs are not mapped. -/
def enterTree (permission : Permission Key)
    (action : Computation n Key Payload Response Value) :
    Computation (n + 1) Key Payload Response Value :=
  FreshBoundaries.mapRequests (enter permission) action

/-- The existing shallow handler, applied to an incoming action after its own
fresh boundary. Resumptions still contain the original, unhandled action. -/
def handleIncoming [DecidableEq Key] (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (action : Computation n Key Payload Response Value) :
    Computation (n + 1) Key Payload Response Result :=
  Computation.shallowHandle arms onReturn onOperation (enterTree permission action)

/-- Removing every statically denied arm leaves the whole runtime unchanged,
including continuations of forwarded requests and all permitted dispatches. -/
theorem discard_denied_arms [DecidableEq Key] (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (action : Computation n Key Payload Response Value) :
    handleIncoming permission arms onReturn onOperation action =
      handleIncoming permission (permittedArms permission arms) onReturn onOperation action := by
  induction action with
  | pure _ => rfl
  | request occurrence payload resume ih =>
    simp only [handleIncoming, enterTree, FreshBoundaries.mapRequests, Computation.shallowHandle,
      capture_permittedArms_iff permission arms occurrence]
    by_cases captured : Capturable (permittedArms permission arms) (enter permission occurrence)
    · simp only [captured, ↓reduceIte]
    · simp only [captured, ↓reduceIte]
      exact congrArg (Computation.request (enter permission occurrence) payload) (funext ih)

/-- Denied arm bodies cannot affect any result: the runtime never calls them.
The two operation interpreters need agree only on keys allowed by the mask. -/
theorem denied_arm_bodies_irrelevant [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (left right : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (agree : ∀ occurrence payload resume, permission occurrence.key = true →
      left occurrence payload resume = right occurrence payload resume)
    (action : Computation n Key Payload Response Value) :
    handleIncoming permission arms onReturn left action =
      handleIncoming permission arms onReturn right action := by
  induction action with
  | pure _ => rfl
  | request occurrence payload resume ih =>
    simp only [handleIncoming, enterTree, FreshBoundaries.mapRequests, Computation.shallowHandle]
    by_cases captured : Capturable arms (enter permission occurrence)
    · simp only [captured, ↓reduceIte]
      exact agree _ _ _ ((enter_capture_iff permission arms occurrence).mp captured).2
    · simp only [captured, ↓reduceIte]
      exact congrArg (Computation.request (enter permission occurrence) payload) (funext ih)

/-- An allowed, already-visible request executes its actual operation arm.
Other denied arms do not change this operational equation. -/
theorem permitted_request_dispatches [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response Value)
    (visible : Capturable arms occurrence) (allowed : permission occurrence.key = true) :
    handleIncoming permission arms onReturn onOperation (.request occurrence payload resume) =
      onOperation (enter permission occurrence) payload
        (fun response => enterTree permission (resume response)) := by
  have captured := (enter_capture_iff permission arms occurrence).mpr ⟨visible, allowed⟩
  simp only [handleIncoming, enterTree, FreshBoundaries.mapRequests, Computation.shallowHandle,
    captured, ↓reduceIte]

/-- Denied requests are forwarded with the boundary intact. The handler waits
around their continuation rather than calling the denied arm. -/
theorem denied_request_forwarded [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response Value)
    (denied : permission occurrence.key = false) :
    handleIncoming permission arms onReturn onOperation (.request occurrence payload resume) =
      .request (enter permission occurrence) payload
        (fun response => handleIncoming permission arms onReturn onOperation (resume response)) := by
  simp only [handleIncoming, enterTree, FreshBoundaries.mapRequests, Computation.shallowHandle,
    denied_never_captured permission arms occurrence denied, ↓reduceIte]

/-- Even an allowed key is forwarded when an older coordinate is nonzero. -/
theorem old_nonzero_request_forwarded [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response Value)
    (coordinate : Fin n) (nonzero : occurrence.weights coordinate ≠ 0) :
    handleIncoming permission arms onReturn onOperation (.request occurrence payload resume) =
      .request (enter permission occurrence) payload
        (fun response => handleIncoming permission arms onReturn onOperation (resume response)) := by
  simp only [handleIncoming, enterTree, FreshBoundaries.mapRequests, Computation.shallowHandle,
    old_nonzero_blocks permission arms occurrence coordinate nonzero, ↓reduceIte]

/-- Resuming a permitted request receives the original incoming continuation,
without reinstalling this shallow handler or checking its arms again. -/
theorem permitted_resume_is_original [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response Value)
    (visible : Capturable arms occurrence) (allowed : permission occurrence.key = true)
    (response : Response) :
    handleIncoming permission arms Computation.pure
      (fun _ _ continuation => continuation response) (.request occurrence payload resume) =
      enterTree permission (resume response) :=
  permitted_request_dispatches permission arms _ _ occurrence payload resume visible allowed

/-- A rejected singleton arm is entirely inert for every incoming tree. -/
theorem denied_handler_is_bind [DecidableEq Key]
    (permission : Permission Key) (key : Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (action : Computation n Key Payload Response Value) (denied : permission key = false) :
    handleIncoming permission [key] onReturn onOperation action =
      (enterTree permission action).bind onReturn := by
  induction action with
  | pure _ => rfl
  | request occurrence payload resume ih =>
    have blocked : ¬ Capturable [key] (enter permission occurrence) := by
      intro captured
      have info := (enter_capture_iff permission [key] occurrence).mp captured
      have sameKey : occurrence.key = key := by simpa using info.1.1
      simp only [sameKey, denied, Bool.false_eq_true, and_false] at info
    simp only [handleIncoming, enterTree, FreshBoundaries.mapRequests,
      Computation.shallowHandle, blocked, ↓reduceIte, Computation.bind]
    exact congrArg (Computation.request (enter permission occurrence) payload) (funext ih)

/-- Boundary checking is run before the same incoming-action handler. The
error branch reports denied keys rather than silently dropping their arms. -/
def checkedHandleIncoming [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (action : Computation n Key Payload Response Value) :
    Except (List Key) (Computation (n + 1) Key Payload Response Result) :=
  if check permission arms then
    .ok (handleIncoming permission arms onReturn onOperation action)
  else .error (diagnostics permission arms)

theorem checkedHandleIncoming_success_iff [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (action : Computation n Key Payload Response Value)
    (result : Computation (n + 1) Key Payload Response Result) :
    checkedHandleIncoming permission arms onReturn onOperation action = .ok result ↔
      Permitted permission arms ∧
        handleIncoming permission arms onReturn onOperation action = result := by
  cases accepted : check permission arms <;>
    simp [checkedHandleIncoming, accepted, ← check_exact]

theorem checkedHandleIncoming_error_iff [DecidableEq Key]
    (permission : Permission Key) (arms : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (action : Computation n Key Payload Response Value) (errors : List Key) :
    checkedHandleIncoming permission arms onReturn onOperation action = .error errors ↔
      errors = diagnostics permission arms ∧ errors ≠ [] := by
  cases accepted : check permission arms with
  | false =>
      have notEmpty : diagnostics permission arms ≠ [] := by
        intro empty
        have pass := (diagnostics_empty_iff permission arms).mp empty
        simp only [accepted, Bool.false_eq_true] at pass
      simp only [checkedHandleIncoming, accepted, Bool.false_eq_true, ↓reduceIte,
        Except.error.injEq]
      exact ⟨fun equal => ⟨equal.symm, fun empty => notEmpty (equal.trans empty)⟩,
        fun ⟨equal, _⟩ => equal.symm⟩
  | true =>
      have empty := (diagnostics_empty_iff permission arms).mpr accepted
      simp [checkedHandleIncoming, accepted, empty]

end Yulang.HandlerPermissions
