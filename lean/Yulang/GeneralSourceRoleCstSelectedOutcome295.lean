import Yulang.GeneralSourceRoleCstExplicitRead295

/-! Preserve failure stages for an optional frontend adapter. In particular,
a producer failure is not a semantic rejection by the Rust compiler. -/
namespace Yulang.GeneralSourceRoleCstSelectedOutcome295
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary captureAt checked checked_exact)
open GeneralSourceRoleCstNamingScope295 (symbolic)
open GeneralSourceRoleCstNamingTrace295 (capture)
open GeneralSourceRoleCstSelectedCompile295 (handoff compile)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleTrack292 (runTracked)
open GeneralSourceMetadataRoles291 (RoleSource)

inductive Error where
  | badJson (reason : String)
  | schemaOrDepth
  | selectionOrRecovery
  | unsupportedSymbolic
  | namingMismatch
  | oldExportRejected
  deriving DecidableEq, Repr

def run {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy) (scope : S)
    (w : Wire) (brand : B) (a : Address B) (sealed : FiniteBoundary S B)
    (env : S → Environment) (fallback : Nat) : Except Error RoleSource :=
  match handoff policy scope w brand a sealed.selected with
  | none => .error .selectionOrRecovery
  | some picked => match symbolic picked with
    | none => .error .unsupportedSymbolic
    | some r =>
      if capture (env r.scope) r.role = sealed.naming then
        match runTracked env fallback [picked] with
        | none => .error .oldExportRejected
        | some table => .ok table
      else .error .namingMismatch

theorem ok_iff_checked {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy) (scope : S)
    (w : Wire) (brand : B) (a : Address B) (sealed : FiniteBoundary S B)
    (env : S → Environment) (fallback : Nat) (table : RoleSource) :
    run policy scope w brand a sealed env fallback = .ok table ↔
      checked policy scope w brand a sealed env fallback = some table := by
  rw [checked_exact]
  cases h : handoff policy scope w brand a sealed.selected with
  | none => simp [run,h,captureAt]
  | some p =>
    cases r : symbolic p with
    | none => simp [run,h,r,captureAt]
    | some v =>
      by_cases matchTrace : capture (env v.scope) v.role = sealed.naming
      · cases done : runTracked env fallback [p] <;>
          simp [run,h,r,matchTrace,done,captureAt,compile]
      · simp [run,h,r,matchTrace,captureAt]

theorem rejects_selection_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a sealed env fallback = .error .selectionOrRecovery ↔
      handoff policy scope w brand a sealed.selected = none := by
  cases h : handoff policy scope w brand a sealed.selected with
  | none => simp [run,h]
  | some p =>
    cases r : symbolic p with
    | none => simp [run,h,r]
    | some v =>
      by_cases eq : capture (env v.scope) v.role = sealed.naming
      · cases done : runTracked env fallback [p] <;> simp [run,h,r,eq,done]
      · simp [run,h,r,eq]

theorem rejects_changed_naming {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) (trace : GeneralSourceRoleCstNamingTrace295.Trace)
    (supplied : captureAt policy scope w brand a sealed.selected env = some trace)
    (wrong : trace ≠ sealed.naming) :
    run policy scope w brand a sealed env fallback = .error .namingMismatch := by
  obtain ⟨p,r,ready,source,obs⟩ :=
    (GeneralSourceRoleCstNamingPacket295.capture_at_exact ..).mp supplied
  simp [run,ready,source,obs,wrong]

end Yulang.GeneralSourceRoleCstSelectedOutcome295
