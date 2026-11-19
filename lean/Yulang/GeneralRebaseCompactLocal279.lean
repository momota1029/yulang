import Yulang.GeneralRebaseCompactMerged279

set_option maxRecDepth 24000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralRebaseCompactLocal279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseCompactDiagnostics279
open GeneralRebaseCompactEdgeInstall279 (replaceEdges reduced)
open GeneralRebaseInstallNovelty279 (Edge)
open CommonRoleOutermostResolver (Frontier)

variable {roles : Roles.RoleDecls} {state : State roles} {new : List (Edge roles)}
variable {registry : Registry} {root : Occurrence roles}

abbrev B := GeneralNominalVersionedDiagnostic232.boundary
abbrev V7 := GeneralNominalVersionedDiagnostic232.v7
abbrev V6 := GeneralNominalVersionedDiagnostic232.v6

theorem root_k2 : (B roles).RootK2 registry (replaceEdges state new) root ↔
    (B roles).RootK2 registry state root := by
  change (_ ∨ GeneralNominalVersionedCycles232.RootCycle (replaceEdges state new) root) ↔
    (_ ∨ GeneralNominalVersionedCycles232.RootCycle state root)
  rw [root_cycle_iff]
  rfl

theorem candidate_k2 : (B roles).CandidateK2 registry (replaceEdges state new) root ↔
    (B roles).CandidateK2 registry state root := by
  change (_ ∨ GeneralNominalVersionedCycles232.CandidateCycle registry (replaceEdges state new) root) ↔
    (_ ∨ GeneralNominalVersionedCycles232.CandidateCycle registry state root)
  rw [candidate_cycle_iff]
  rfl

theorem inspection_pending : (B roles).InspectionPending registry (replaceEdges state new) root ↔
    (B roles).InspectionPending registry state root := by
  change (_ ∨ ¬ GeneralNominalVersionedDiagnostic232.AdministrativeReady (replaceEdges state new) root) ↔
    (_ ∨ ¬ GeneralNominalVersionedDiagnostic232.AdministrativeReady state root)
  rw [administrative_iff]
  rfl

theorem safe_known : B4TargetV8.SafeKnown (B roles) registry (replaceEdges state new) root ↔
    B4TargetV8.SafeKnown (B roles) registry state root := by
  unfold B4TargetV8.SafeKnown B4TargetV7.SafeKnown B4TargetV6.SafeKnown B4Target.SafeKnown
  simp only [root_k2 (registry := registry),candidate_k2 (registry := registry),
    inspection_pending (registry := registry)]
  rfl

theorem v6_root : (V6 roles).RootK2 registry (replaceEdges state new) root ↔
    (V6 roles).RootK2 registry state root := root_k2

theorem v6_candidate : (V6 roles).CandidateK2 registry (replaceEdges state new) root ↔
    (V6 roles).CandidateK2 registry state root := candidate_k2

theorem v6_pending : (V6 roles).InspectionPending registry (replaceEdges state new) root ↔
    (V6 roles).InspectionPending registry state root := inspection_pending

theorem v7_root : (V7 roles).RootK2 registry (replaceEdges state new) root ↔
    (V7 roles).RootK2 registry state root := root_k2

theorem v7_candidate : (V7 roles).CandidateK2 registry (replaceEdges state new) root ↔
    (V7 roles).CandidateK2 registry state root := candidate_k2

theorem v7_safe : B4TargetV7.SafeKnown (V7 roles) registry (replaceEdges state new) root ↔
    B4TargetV7.SafeKnown (V7 roles) registry state root := safe_known

theorem v6_reject : B4TargetV6.RejectReason (V6 roles) registry (replaceEdges state new) root ↔
    B4TargetV6.RejectReason (V6 roles) registry state root := by
  unfold B4TargetV6.RejectReason
  simp only [v6_root,v6_candidate,v6_pending]
  have output (key : Nat) :
    (V6 roles).OutputConflict registry (replaceEdges state new) root key ↔
      (V6 roles).OutputConflict registry state root key := output_conflict_iff
  simp only [output]
  rfl

theorem v6_local (frontier : Frontier (GeneralNominalVersionedDiagnostic232.vocabulary roles).Demand) :
    B4TargetV6.Local (V6 roles) registry (replaceEdges state new) root frontier ↔
    B4TargetV6.Local (V6 roles) registry state root frontier := by
  constructor <;> intro chosen
  · cases chosen with
    | pending h => exact .pending h
    | inspectionPending a b c d =>
      exact .inspectionPending a (inspection_pending.mp b) ((not_congr root_k2).mp c)
        ((not_congr candidate_k2).mp d)
    | rejected h => exact .rejected (v6_reject.mp h)
    | ambiguous s a b ne => exact .ambiguous (safe_known.mp s) a b ne
    | selected s u clear => exact .selected (safe_known.mp s) u ((not_congr output_conflict_iff).mp clear)
  · cases chosen with
    | pending h => exact .pending h
    | inspectionPending a b c d =>
      exact .inspectionPending a (inspection_pending.mpr b) ((not_congr root_k2).mpr c)
        ((not_congr candidate_k2).mpr d)
    | rejected h => exact .rejected (v6_reject.mpr h)
    | ambiguous s a b ne => exact .ambiguous (safe_known.mpr s) a b ne
    | selected s u clear => exact .selected (safe_known.mpr s) u ((not_congr output_conflict_iff).mpr clear)

theorem v7_priority : B4TargetV7.PriorityAmbiguity (V7 roles) registry (replaceEdges state new) root ↔
    B4TargetV7.PriorityAmbiguity (V7 roles) registry state root := by
  unfold B4TargetV7.PriorityAmbiguity
  simp only [v7_root,v7_candidate]
  rfl

theorem v7_local (frontier : Frontier (GeneralNominalVersionedDiagnostic232.vocabulary roles).Demand) :
    B4TargetV7.Local (V7 roles) registry (replaceEdges state new) root frontier ↔
    B4TargetV7.Local (V7 roles) registry state root frontier :=
  B4TargetV7.local_transport v6_local GeneralRebaseCompactMerged279.conflict_iff v7_priority frontier

theorem sharing :
    (B roles).SharingConflict registry (replaceEdges state new) root ↔ (B roles).SharingConflict registry state root := by
  change GeneralNominalVersionedDiagnostic232.SharingConflict registry (replaceEdges state new) root ↔
    GeneralNominalVersionedDiagnostic232.SharingConflict registry state root
  unfold GeneralNominalVersionedDiagnostic232.SharingConflict
  simp only [v7_safe,at_key_iff]
  rfl

theorem v8_priority : B4TargetV8.PriorityAmbiguity (B roles) registry (replaceEdges state new) root ↔
    B4TargetV8.PriorityAmbiguity (B roles) registry state root := v7_priority

theorem exact (frontier : Frontier (GeneralNominalVersionedDiagnostic232.vocabulary roles).Demand) :
    GeneralNominalVersionedDiagnostic232.Local registry (replaceEdges state new) root frontier ↔
    GeneralNominalVersionedDiagnostic232.Local registry state root frontier :=
  B4TargetV8.local_transport v7_local sharing v8_priority frontier

theorem adapter (frontier : Frontier (GeneralNominalVersionedDiagnostic232.vocabulary roles).Demand) :
    GeneralNominalVersionedMixedSourceBoundary234.Local registry (replaceEdges state new) root frontier ↔
    GeneralNominalVersionedMixedSourceBoundary234.Local registry state root frontier := by
  exact GeneralNominalVersionedMixedSourceBoundary234.local_iff.trans
    (GeneralNominalVersionedMixedBoundary234.local_iff.trans
      ((exact frontier).trans (GeneralNominalVersionedMixedBoundary234.local_iff.symm.trans
        GeneralNominalVersionedMixedSourceBoundary234.local_iff.symm)))

end Yulang.GeneralRebaseCompactLocal279
