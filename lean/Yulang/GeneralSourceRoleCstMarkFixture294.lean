import Yulang.GeneralSourceRoleCstReportWire294

/-! Synthetic controls for strict/branch policy contrast and explicit
ancestor ownership. Actual checked-in golden is replayed by the CLI. -/
namespace Yulang.GeneralSourceRoleCstMarkFixture294
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address)
open GeneralSourceRoleCstRustFixture293 (actualRole expected)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleCstMarkReport294 (run)
open GeneralSourceRoleCstMarkPolicy294 (guarded Policy)
open GeneralSourceRoleCstMarkScope294 (Zone)

def clean : Snapshot Nat := ⟨10,.node .root [actualRole]⟩
def after : Snapshot Nat := ⟨10,.node .root [actualRole,.token .error ":",.node .missing []]⟩
def wrappedError : Snapshot Nat := ⟨10,.node .root [.node .error [actualRole]]⟩

theorem clean_agreement :
    (run () clean ⟨10,[0]⟩).admitted .whole = some expected ∧
    (run () clean ⟨10,[0]⟩).admitted .selectedBranch = some expected := ⟨rfl,rfl⟩

theorem unrelated_marks_survive_projection :
    (run () after ⟨10,[0]⟩).wholeWireMarkFree = false ∧
    (run () after ⟨10,[0]⟩).selectedBranchMarkFree = true ∧
    (run () after ⟨10,[0]⟩).admitted .whole = none ∧
    (run () after ⟨10,[0]⟩).admitted .selectedBranch = some expected ∧
    ((run () after ⟨10,[0]⟩).found.map Prod.fst) = [.unrelated,.unrelated] :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem ancestor_really_blocks_selected_branch :
    (run () wrappedError ⟨10,[0,0]⟩).projected.isSome = true ∧
    ((run () wrappedError ⟨10,[0,0]⟩).found.map Prod.fst) = [.ancestor] ∧
    (run () wrappedError ⟨10,[0,0]⟩).admitted .selectedBranch = none :=
  ⟨rfl,rfl,rfl⟩

theorem no_marks_not_same_as_valid_address :
    (run () clean ⟨11,[0]⟩).wholeWireMarkFree = true ∧
    (run () clean ⟨11,[0]⟩).projected = none ∧
    (run () clean ⟨10,[5]⟩).admitted .selectedBranch = none :=
  ⟨rfl,rfl,rfl⟩

#guard (run () after ⟨10,[0]⟩).selectedBranchMarkFree
#guard !(run () wrappedError ⟨10,[0,0]⟩).selectedBranchMarkFree

end Yulang.GeneralSourceRoleCstMarkFixture294
