import Yulang.GeneralSourceRoleCstSymbolicTotal295

/-! Separate the concrete successful wrapped fragment from generic fallback
error labels. It cannot lose its symbolic role after selection succeeds. -/
namespace Yulang.GeneralSourceRoleCstOutcomePrecise295
open GeneralSourceRoleCstSelectedOutcome295 (Error run)
open GeneralSourceRoleCstSelectedCompile295 (handoff compile)
open GeneralSourceRoleCstNamingScope295 (symbolic)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary captureAt)
open GeneralSourceRoleCstNamingTrace295 (capture)
open GeneralSourceRoleCstSymbolicTotal295 (handoff_goes_symbolic)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleTrack292 (runTracked)

theorem never_unsupported_symbolic {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a packet env fallback ≠ .error .unsupportedSymbolic := by
  cases h : handoff policy scope w brand a packet.selected with
  | none => simp [run,h]
  | some p =>
    obtain ⟨r,selected,_⟩ := handoff_goes_symbolic policy scope w brand a packet.selected p h
    by_cases same : capture (env r.scope) r.role = packet.naming
    · cases done : runTracked env fallback [p] <;> simp [run,h,selected,same,done]
    · simp [run,h,selected,same]

theorem naming_mismatch_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a packet env fallback = .error .namingMismatch ↔
      ∃ t, captureAt policy scope w brand a packet.selected env = some t ∧ t ≠ packet.naming := by
  cases h : handoff policy scope w brand a packet.selected with
  | none => simp [run,h,captureAt]
  | some p =>
    obtain ⟨r,selected,_⟩ := handoff_goes_symbolic policy scope w brand a packet.selected p h
    by_cases same : capture (env r.scope) r.role = packet.naming
    · cases done : runTracked env fallback [p] <;> simp [run,h,selected,same,done,captureAt]
    · simp [run,h,selected,same,captureAt]

theorem old_export_rejection_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a packet env fallback = .error .oldExportRejected ↔
      captureAt policy scope w brand a packet.selected env = some packet.naming ∧
      compile policy scope w brand a packet.selected env fallback = none := by
  cases h : handoff policy scope w brand a packet.selected with
  | none => simp [run,h,captureAt]
  | some p =>
    obtain ⟨r,selected,_⟩ := handoff_goes_symbolic policy scope w brand a packet.selected p h
    by_cases same : capture (env r.scope) r.role = packet.naming
    · cases done : runTracked env fallback [p] <;> simp [run,h,selected,same,done,captureAt,compile]
    · simp [run,h,selected,same,captureAt]

end Yulang.GeneralSourceRoleCstOutcomePrecise295
