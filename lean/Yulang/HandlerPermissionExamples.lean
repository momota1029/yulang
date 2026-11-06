import Yulang.HandlerPermissions

/-!
# Decision-41 examples at an annotated incoming-action boundary

The mixed handler models `catch a` when `a` permits `console` but not `io`.
Its `io` arm receives a diagnostic while its `console` arm still has the usual
dispatch equation. Old positive and negative weights remain significant, and
locally emitted arm effects are neither boundary-protected nor recursively
handled. The examples use actual `Directed.Computation` evaluation.
-/

namespace Yulang.HandlerPermissionExamples

open Directed HandlerPermissions

inductive Key where
  | console
  | io
  | undet
  deriving DecidableEq, BEq, Repr

def onlyConsole : Permission Key := fun key => key == .console

abbrev Incoming := Computation 1 Key Nat Nat Nat
abbrev Scoped := Computation 2 Key Nat Nat Nat

def oldScope : Fin 1 := 0

def request (key : Key) : Incoming := .request (raw key) 7 (fun response => .pure response)

def onReturn (value : Nat) : Scoped := .pure value

def onOperation (occurrence : Occurrence 2 Key) (payload : Nat)
    (_resume : Nat → Scoped) : Scoped :=
  match occurrence.key with
  | .console => .pure (payload + 10)
  | .io => .pure 100
  | .undet => .pure 200

def arms : List Key := [.console, .io]

theorem mixed_annotation_reports_only_io :
    diagnostics onlyConsole arms = [.io] := by decide

theorem mixed_annotation_rejected : check onlyConsole arms = false := by decide

theorem permitted_console_arm_remains :
    permittedArms onlyConsole arms = [.console] := by decide

/-- Error recovery does not change the valid arm's operational meaning. -/
theorem console_dispatches_despite_io_error :
    handleIncoming onlyConsole arms onReturn onOperation (request .console) = .pure 17 := by
  apply permitted_request_dispatches onlyConsole arms onReturn onOperation
    (raw (n := 1) Key.console) 7 (fun response => .pure response)
  · simp [Capturable, raw, arms]
  · rfl

theorem io_is_forwarded_with_fresh_barrier :
    handleIncoming onlyConsole arms onReturn onOperation (request .io) =
      .request (enter onlyConsole (raw Key.io)) 7 (fun response => .pure response) := by
  exact denied_request_forwarded onlyConsole arms onReturn onOperation
    (raw (n := 1) Key.io) 7 (fun response => .pure response) rfl

theorem rejected_entry_returns_diagnostic :
    checkedHandleIncoming onlyConsole arms onReturn onOperation (request .console) =
      .error [.io] := by
  rfl

theorem accepted_entry_really_runs :
    checkedHandleIncoming onlyConsole [.console] onReturn onOperation (request .console) =
      .ok (.pure 17) := by
  rfl

def withDebt : Incoming :=
  .request (release oldScope allowNone (raw .console)) 7 (fun response => .pure response)

def withProtection : Incoming :=
  .request (protect oldScope allowNone (raw .console)) 7 (fun response => .pure response)

theorem permission_does_not_cancel_old_debt :
    handleIncoming onlyConsole [.console] onReturn onOperation withDebt =
      .request (enter onlyConsole (release oldScope allowNone (raw .console))) 7
        (fun response => .pure response) := by
  apply old_nonzero_request_forwarded onlyConsole [.console] onReturn onOperation
    _ 7 (fun response => .pure response) oldScope
  decide

theorem permission_does_not_cancel_old_protection :
    handleIncoming onlyConsole [.console] onReturn onOperation withProtection =
      .request (enter onlyConsole (protect oldScope allowNone (raw .console))) 7
        (fun response => .pure response) := by
  apply old_nonzero_request_forwarded onlyConsole [.console] onReturn onOperation
    _ 7 (fun response => .pure response) oldScope
  decide

/-- The arm's locally emitted io request is outside the incoming boundary. -/
theorem local_arm_effect_is_not_masked :
    handleIncoming onlyConsole [.console] onReturn
      (fun _ _ _ => .request (raw .io) 8 (fun response => .pure response)) (request .console) =
      (.request (raw .io) 8 (fun response => .pure response) : Scoped) := by
  apply permitted_request_dispatches
  · simp [Capturable, raw]
  · rfl

/-- A newly emitted request for the same handled key is still outside this
shallow handler. It is not captured again merely because the key is permitted. -/
theorem reemitted_console_escapes_shallow_handler :
    handleIncoming onlyConsole [.console] onReturn
      (fun _ _ _ => .request (raw .console) 8 (fun response => .pure response)) (request .console) =
      (.request (raw .console) 8 (fun response => .pure response) : Scoped) := by
  apply permitted_request_dispatches
  · simp [Capturable, raw]
  · rfl

def twoRequests : Incoming :=
  .request (raw .console) 7 (fun _ => request .console)

theorem resumption_is_not_rehandled :
    handleIncoming onlyConsole [.console] Computation.pure
      (fun _ _ resume => resume 4) twoRequests = enterTree onlyConsole (request .console) := by
  apply permitted_resume_is_original
  · simp [Capturable, raw]
  · rfl

inductive Head where
  | returned : Nat → Head
  | forwarded : Key → Int → Int → Nat → Head
  deriving DecidableEq, BEq, Repr

def inspect (computation : Scoped) : Head :=
  match computation with
  | .pure value => .returned value
  | .request occurrence payload _ =>
      .forwarded occurrence.key (occurrence.weights 0) (occurrence.weights 1) payload

/-- These executable checks inspect the same runtime as the general proofs. -/
def runtimeCases : List (String × Head × Head) :=
  [ ("allowed console dispatches despite io diagnostic",
      inspect (handleIncoming onlyConsole arms onReturn onOperation (request .console)),
      .returned 17)
  , ("denied io forwards with new weight +1",
      inspect (handleIncoming onlyConsole arms onReturn onOperation (request .io)),
      .forwarded .io 1 0 7)
  , ("old negative debt survives explicit permission",
      inspect (handleIncoming onlyConsole [.console] onReturn onOperation withDebt),
      .forwarded .console 0 (-1) 7)
  , ("old positive protection survives explicit permission",
      inspect (handleIncoming onlyConsole [.console] onReturn onOperation withProtection),
      .forwarded .console 0 1 7)
  , ("glob permits an unlisted incoming effect family",
      inspect (handleIncoming allowAll [.undet] onReturn onOperation (request .undet)),
      .returned 200)
  , ("unannotated incoming action keeps all requests protected",
      inspect (handleIncoming allowNone [.console] onReturn onOperation (request .console)),
      .forwarded .console 1 0 7)
  , ("local io emitted by the console arm stays unprotected",
      inspect (handleIncoming onlyConsole [.console] onReturn
        (fun _ _ _ => .request (raw .io) 8 (fun response => .pure response)) (request .console)),
      .forwarded .io 0 0 8)
  , ("resumption keeps the next request outside this shallow handler",
      inspect (handleIncoming onlyConsole [.console] Computation.pure
        (fun _ _ resume => resume 4) twoRequests),
      .forwarded .console 0 0 7) ]

theorem runtime_cases_correct :
    ∀ entry ∈ runtimeCases, entry.2.1 = entry.2.2 := by decide

end Yulang.HandlerPermissionExamples
