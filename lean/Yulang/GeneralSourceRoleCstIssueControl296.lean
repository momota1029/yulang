import Yulang.GeneralSourceRoleCstIssuePacket296

/-! Closed checks of replay identity. A different revision is distinct from a
new failure at the original revision's independently checked recovery gate. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace Yulang.GeneralSourceRoleCstIssueControl296
open GeneralSourceRoleCstIssuedScope296 (Packet accept)
open GeneralSourceRoleCstIssuePacket296 (Issued issue)
open GeneralSourceRoleCstSelectedControl295 (first second both packet)
open GeneralSourceRoleCstCatalogControl296 (irrelevant binder)
open GeneralSourceRoleCstNamingPacketFixture295 (binderTrace)
open GeneralSourceRoleResolverFixture292 (parameterTable)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)

def issued : Issued Nat Nat Nat :=
  ⟨⟨both,5,first,.selectedBranch,41,2,binder⟩,⟨binderTrace,parameterTable⟩⟩

def noDiagnosticObservation : Boundary Nat Nat :=
  ⟨5,⟨first,.selectedBranch,⟨both,.absent⟩⟩⟩

theorem issued_contains_only_demanded_rows :
    issue .selectedBranch 5 both 71 first (41 : Nat) (packet first) irrelevant 2 = .ok issued := rfl

theorem replay_binds_scope_revision_and_fallback :
    accept issued.packet both 5 71 first .selectedBranch 41 (packet first) 2 =
      .ok issued.exportResult ∧
    accept issued.packet both 5 71 first .selectedBranch 42 (packet first) 2 =
      .error .mismatchedScope ∧
    accept issued.packet both 5 71 first .selectedBranch 41 (packet first) 3 =
      .error .mismatchedScope ∧
    accept issued.packet both 5 71 second .selectedBranch 41 (packet second) 2 =
      .error .mismatchedScope := ⟨rfl,rfl,rfl,rfl⟩

theorem issue_does_not_clear_fresh_recovery_gate :
    accept issued.packet both 5 71 first .selectedBranch 41 noDiagnosticObservation 2 =
      .error (.selected .selection) := rfl

end Yulang.GeneralSourceRoleCstIssueControl296
