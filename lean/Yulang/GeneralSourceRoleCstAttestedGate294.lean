import Yulang.GeneralSourceRoleCstDiagnostics294

/-! Combine wire policy with an independent successful diagnostic receipt.
Exactness against authoritative diagnostics is conditional on its attachment. -/
namespace Yulang.GeneralSourceRoleCstAttestedGate294
open GeneralSourceRoleCstSnapshot293 (Snapshot Address)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleCstMarkPolicy294
open GeneralSourceRoleCstRecovery293 (TreePlain)
open GeneralSourceRoleCstDiagnostics294
open GeneralSourceRoleTrack292 (Tracked)

def checked {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (s : Snapshot Brand) (address : Address Brand) (packet : Scan Brand) :
    Option (Tracked Scope (Address Brand)) :=
  if permits policy s.brand address.path packet then guarded policy scope s address else none

theorem checked_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (s : Snapshot Brand) (address : Address Brand) (packet : Scan Brand)
    (out : Tracked Scope (Address Brand)) :
    checked policy scope s address packet = some out ↔
      permits policy s.brand address.path packet = true ∧
      allows policy s.root address.path = true ∧ exportAt scope s address = some out := by
  by_cases h : permits policy s.brand address.path packet = true
  · simp [checked,h,guarded_exact]
  · simp [checked,h]

theorem whole_attached_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (packet : Scan Brand)
    (out : Tracked Scope (Address Brand)) (authoritative : List Diagnostic)
    (attached : packet = .reported s.brand authoritative) :
    checked .whole scope s a packet = some out ↔
      authoritative = [] ∧ TreePlain s.root ∧ exportAt scope s a = some out := by
  rw [checked_exact,whole_report_exact,whole_exact,attached]
  simp

theorem branch_attached_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (packet : Scan Brand)
    (out : Tracked Scope (Address Brand)) (authoritative : List Diagnostic)
    (attached : packet = .reported s.brand authoritative) :
    checked .selectedBranch scope s a packet = some out ↔
      (∀ d ∈ authoritative, IndependentPermission .selectedBranch a.path d) ∧
      BranchPlain s.root a.path ∧ exportAt scope s a = some out := by
  rw [checked_exact,permits_exact,attached]
  simp only [Scan.reported.injEq,true_and]
  constructor
  · rintro ⟨⟨_,rfl,permit⟩,wire,found⟩
    exact ⟨permit,(branch_exact ..).mp wire,found⟩
  · rintro ⟨permit,wire,found⟩
    exact ⟨⟨authoritative,rfl,permit⟩,(branch_exact ..).mpr wire,found⟩

theorem checked_cannot_create_projection {Scope Brand : Type} [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (s : Snapshot Brand) (a : Address Brand) (scan : Scan Brand)
    (out : Tracked Scope (Address Brand)) (done : checked policy scope s a scan = some out) :
    exportAt scope s a = some out := ((checked_exact ..).mp done).2.2

end Yulang.GeneralSourceRoleCstAttestedGate294
