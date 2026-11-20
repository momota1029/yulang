import Yulang.GeneralSourceRoleCstAttestedGate294

/-! Distinguish the same mark-free tree under two supplied diagnostic lists.
This is an adapter control, not a fresh Rust diagnostic run. -/
namespace Yulang.GeneralSourceRoleCstDiagnosticFixture294
open GeneralSourceRoleCstSnapshot293 (Snapshot Address)
open GeneralSourceRoleCstRustFixture293 (actualRole)
open GeneralSourceRoleCstMarkPolicy294 (allows Policy guarded)
open GeneralSourceRoleCstDiagnostics294 (Scan Diagnostic)
open GeneralSourceRoleCstAttestedGate294 (checked)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)

def ordinaryHeader : Snapshot Nat :=
  ⟨10,.node .root [.node .other [.token .identifier "<+>"],actualRole]⟩
def site : Address Nat := ⟨10,[1]⟩
def cleanPacket : Scan Nat := .reported 10 []
def headerConflict : Diagnostic := ⟨.conflictingOperator,some [0]⟩
def withConflict : Scan Nat := .reported 10 [headerConflict]
def unknownSite : Scan Nat := .reported 10 [⟨.conflictingOperator,none⟩]

theorem mark_free_not_enough_for_diagnostic_admission :
    allows .whole ordinaryHeader.root site.path = true ∧
    (checked .whole () ordinaryHeader site cleanPacket).isSome = true ∧
    checked .whole () ordinaryHeader site withConflict = none := ⟨rfl,rfl,rfl⟩

theorem selected_can_use_only_independent_unrelated_ownership :
    (checked .selectedBranch () ordinaryHeader site withConflict).isSome = true ∧
    checked .selectedBranch () ordinaryHeader site unknownSite = none := ⟨rfl,rfl⟩

theorem absent_failed_foreign_distinct_from_success :
    checked .whole () ordinaryHeader site (.absent : Scan Nat) = none ∧
    checked .whole () ordinaryHeader site (.failed : Scan Nat) = none ∧
    checked .whole () ordinaryHeader site (.reported 11 []) = none ∧
    (checked .whole () ordinaryHeader site (.reported 10 [])).isSome = true :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem same_wire_cannot_compute_attached_affected_scope :
    ¬ ∃ fromWire : Snapshot Nat → Bool,
        fromWire ordinaryHeader = (checked .whole () ordinaryHeader site cleanPacket).isSome ∧
        fromWire ordinaryHeader = (checked .whole () ordinaryHeader site withConflict).isSome := by
  rintro ⟨guess,a,b⟩
  have impossible : true = false := a.symm.trans b
  cases impossible

#guard !(checked .selectedBranch () ordinaryHeader site unknownSite).isSome

end Yulang.GeneralSourceRoleCstDiagnosticFixture294
