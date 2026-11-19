import Yulang.GeneralRebaseArchiveConflict280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseArchiveLocal280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open CommonRoleOutermostResolver (Frontier)
open GeneralRebaseArchiveTrust280 (Correspond changeEffects)
open GeneralRebaseArchiveGuards280 (root_k2 candidate_k2 pending safe_known)
open GeneralRebaseArchiveConflict280 (output merged at_key)
open GeneralNominalVersionedDiagnostic232 (boundary v6 v7 Local vocabulary)

variable {roles : Roles.RoleDecls} {s : State roles} {ys : List (Effect roles)}
variable {r : Registry} {root : Occurrence roles}

theorem root6 (pairs : Correspond s.effects ys) :
    (v6 roles).RootK2 r s root ↔ (v6 roles).RootK2 r (changeEffects s ys) root :=
  root_k2 pairs _ _

theorem candidate6 (pairs : Correspond s.effects ys) :
    (v6 roles).CandidateK2 r s root ↔ (v6 roles).CandidateK2 r (changeEffects s ys) root :=
  candidate_k2 pairs _ _

theorem pending6 (pairs : Correspond s.effects ys) :
    (v6 roles).InspectionPending r s root ↔ (v6 roles).InspectionPending r (changeEffects s ys) root :=
  pending pairs _ _

theorem reject6 (pairs : Correspond s.effects ys) :
    B4TargetV6.RejectReason (v6 roles) r s root ↔
      B4TargetV6.RejectReason (v6 roles) r (changeEffects s ys) root := by
  unfold B4TargetV6.RejectReason
  simp only [root6 pairs,candidate6 pairs,pending6 pairs]
  have out (key : Nat) :
    (v6 roles).OutputConflict r s root key ↔ (v6 roles).OutputConflict r (changeEffects s ys) root key :=
    output pairs r root key
  simp only [out]
  rfl

theorem local6 (pairs : Correspond s.effects ys) (f : Frontier (vocabulary roles).Demand) :
    B4TargetV6.Local (v6 roles) r s root f ↔ B4TargetV6.Local (v6 roles) r (changeEffects s ys) root f := by
  constructor <;> intro localCert
  · cases localCert with
    | pending h => exact .pending h
    | inspectionPending a b c d =>
      exact .inspectionPending a ((pending pairs _ _).mp b) ((not_congr (root_k2 pairs _ _)).mp c)
        ((not_congr (candidate_k2 pairs _ _)).mp d)
    | rejected h => exact .rejected ((reject6 pairs).mp h)
    | ambiguous h a b ne => exact .ambiguous ((safe_known pairs _ _).mp h) a b ne
    | selected h u clear => exact .selected ((safe_known pairs _ _).mp h) u ((not_congr (output pairs _ _ _)).mp clear)
  · cases localCert with
    | pending h => exact .pending h
    | inspectionPending a b c d =>
      exact .inspectionPending a ((pending pairs _ _).mpr b) ((not_congr (root_k2 pairs _ _)).mpr c)
        ((not_congr (candidate_k2 pairs _ _)).mpr d)
    | rejected h => exact .rejected ((reject6 pairs).mpr h)
    | ambiguous h a b ne => exact .ambiguous ((safe_known pairs _ _).mpr h) a b ne
    | selected h u clear => exact .selected ((safe_known pairs _ _).mpr h) u ((not_congr (output pairs _ _ _)).mpr clear)

theorem root7 (pairs : Correspond s.effects ys) :
    (v7 roles).RootK2 r s root ↔ (v7 roles).RootK2 r (changeEffects s ys) root :=
  root_k2 pairs _ _

theorem candidate7 (pairs : Correspond s.effects ys) :
    (v7 roles).CandidateK2 r s root ↔ (v7 roles).CandidateK2 r (changeEffects s ys) root :=
  candidate_k2 pairs _ _

theorem priority (pairs : Correspond s.effects ys) :
    B4TargetV7.PriorityAmbiguity (v7 roles) r s root ↔
      B4TargetV7.PriorityAmbiguity (v7 roles) r (changeEffects s ys) root := by
  unfold B4TargetV7.PriorityAmbiguity
  simp only [root7 pairs,candidate7 pairs]
  rfl

theorem local7 (pairs : Correspond s.effects ys) (f : Frontier (vocabulary roles).Demand) :
    B4TargetV7.Local (v7 roles) r s root f ↔ B4TargetV7.Local (v7 roles) r (changeEffects s ys) root f :=
  B4TargetV7.local_transport (local6 pairs) (merged pairs root) (priority pairs) f

theorem sharing (pairs : Correspond s.effects ys) :
    (boundary roles).SharingConflict r s root ↔ (boundary roles).SharingConflict r (changeEffects s ys) root := by
  change GeneralNominalVersionedDiagnostic232.SharingConflict r s root ↔
    GeneralNominalVersionedDiagnostic232.SharingConflict r (changeEffects s ys) root
  unfold GeneralNominalVersionedDiagnostic232.SharingConflict
  have safe : B4TargetV7.SafeKnown (v7 roles) r s root ↔
      B4TargetV7.SafeKnown (v7 roles) r (changeEffects s ys) root := safe_known pairs r root
  simp only [safe,at_key pairs]
  rfl

theorem exact_local (pairs : Correspond s.effects ys) (f : Frontier (vocabulary roles).Demand) :
    Local r s root f ↔ Local r (changeEffects s ys) root f :=
  B4TargetV8.local_transport (local7 pairs) (sharing pairs) (priority pairs) f

theorem related_local {a b : State roles} (related : GeneralRebaseGraphBisim280.Related a b)
    (f : Frontier (vocabulary roles).Demand) :
    Local r a root f ↔ Local r b root f := by
  obtain ⟨xs,ys,rfl,_,pairs⟩ := related
  exact (GeneralRebaseCompactLocal279.exact _).symm.trans
    (exact_local (s := GeneralRebaseCompactEdgeInstall279.replaceEdges a xs) pairs _)

theorem adapter_local {a b : State roles} (related : GeneralRebaseGraphBisim280.Related a b)
    (f : Frontier (vocabulary roles).Demand) :
    GeneralNominalVersionedMixedSourceBoundary234.Local r a root f ↔
      GeneralNominalVersionedMixedSourceBoundary234.Local r b root f := by
  exact GeneralNominalVersionedMixedSourceBoundary234.local_iff.trans
    (GeneralNominalVersionedMixedBoundary234.local_iff.trans
      ((related_local related f).trans (GeneralNominalVersionedMixedBoundary234.local_iff.symm.trans
        GeneralNominalVersionedMixedSourceBoundary234.local_iff.symm)))

end Yulang.GeneralRebaseArchiveLocal280
