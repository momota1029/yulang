import Yulang.GeneralSourceRoleCstBoundOwners294
import Yulang.GeneralSourceRoleCstGroupFixture294

/-! An optional range receipt is only interpreted against a successful decode
of its wire. The receipt must already be authoritative for this snapshot. -/
namespace Yulang.GeneralSourceRoleCstRangeReceipt294
open GeneralSourceRoleCstTree293 (Path Tree)
open GeneralSourceRoleCstWire293 (Wire decode Transfer decode_exact)
open GeneralSourceRoleCstOriginalMarks294 (Origin)
open GeneralSourceRoleCstGroupAnchor294 (unique outside outside_exact origin_for_each)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstDiagnostics294 (Scan)
open GeneralSourceRoleCstAttestedGate294 (checked)
open GeneralSourceRoleCstBoundOwners294 (checkedBound)
open GeneralSourceRoleCstDiagnosticFixture294 (ordinaryHeader site withConflict)
open GeneralSourceRoleCstSnapshot293 (Snapshot)

def check (wire : Wire) (range : Extent) (selected : Path) : Bool :=
  match decode wire with
  | none => false
  | some root =>
    match unique wire root range with
    | none => false
    | some row => outside selected row

theorem check_exact (wire : Wire) (range : Extent) (s : Path) :
    check wire range s = true ↔
      ∃ root row, Transfer wire root ∧ unique wire root range = some row ∧
        ∀ item ∈ row, ¬ s <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: s := by
  constructor
  · intro ok
    cases hw : decode wire with
    | none => simp [check,hw] at ok
    | some root =>
      cases hr : unique wire root range with
      | none => simp [check,hw,hr] at ok
      | some row =>
        exact ⟨root,row,(decode_exact ..).mp hw,hr,(outside_exact ..).mp
          (by simpa [check,hw,hr] using ok)⟩
  · rintro ⟨root,row,transfer,hr,all⟩
    simp [check,(decode_exact ..).mpr transfer,hr,(outside_exact ..).mpr all]

theorem checked_range_sound (wire : Wire) (range : Extent) (s : Path)
    (ok : check wire range s = true) :
    ∃ root row, Transfer wire root ∧
      unique wire root range = some row ∧
      ∀ item ∈ row,
        (¬ s <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: s) ∧
        ∃ val, GeneralSourceRoleCstWirePaths293.atWire item.occurrence.path wire =
            some (.token "Error" val) := by
  obtain ⟨root,row,map,pick,disjoint⟩ := (check_exact ..).mp ok
  exact ⟨root,row,map,pick,fun item mem => ⟨disjoint item mem,origin_for_each map pick mem⟩⟩

def ungroundedPacket : Scan Nat := .reported 10 [⟨.conflictingOperator,some [999]⟩]

theorem prefix_only_cannot_validate_owner :
    (checked .selectedBranch () ordinaryHeader site ungroundedPacket).isSome = true ∧
    checkedBound .selectedBranch () ordinaryHeader site ungroundedPacket = none ∧
    (checkedBound .selectedBranch () ordinaryHeader site withConflict).isSome = true :=
  ⟨rfl,rfl,rfl⟩

theorem invalid_snapshot_refuses_range :
    check (.node "!not-a-tag" [.token "Error" "-"]) ⟨0,1⟩ [1] = false := rfl

open GeneralSourceRoleCstGroupFixture294 (twoRuns)

theorem ambiguous_attachment_refuses_range : check twoRuns ⟨0,0⟩ [1] = false := rfl

end Yulang.GeneralSourceRoleCstRangeReceipt294
