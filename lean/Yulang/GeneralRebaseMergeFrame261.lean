import Yulang.GeneralRebaseMergeRun261
namespace Yulang.GeneralRebaseMergeFrame261
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeStable
open GeneralNominalCenteredHeadAllocMergeConflict (focus chosen chosen_checked current)
open GeneralRebaseMergeRequests261 (candidate packet)

/-- This is the actual inspected leaf packet, not a supplied empty report. -/
theorem report_empty (atoms) : GeneralNominalPacketSupport.report (packet atoms) = {} :=
 GeneralNominalCenteredHeadAllocMergeConflict.empty_report

theorem bindings_empty (atoms) : (packet atoms).bindings = [] := by
 change GeneralNominalRecursiveInspection.bindings (current atoms).state (GeneralNominalPacketSupport.report (packet atoms)) = []
 rw [report_empty]
 rfl

theorem ordinary (atoms) (assignment : Assignment) : GeneralNominalVersionedPlans231.Ordinary (packet atoms) assignment := by
 unfold GeneralNominalVersionedPlans231.Ordinary
 rw [bindings_empty,report_empty]
 simp [GeneralNominalAllocation.Compatible,GeneralNominalVersionedAllocation231.merges,
  GeneralNominalRecursiveInspection.selfChecks,PresenceNormalForm.All,
  show chosen.inputNames = [] from rfl]

theorem head_models (atoms) (assignment : Assignment)
 (valid : GeneralNominalState.Models (current atoms).state assignment) :
 GeneralNominalVersionedPlans231.HeadModels (packet atoms) assignment := by
 refine ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨valid,ordinary atoms assignment⟩,?_⟩
 rw [report_empty]
 simp [GeneralNominalRecursiveInspection.ProjectionModels]

theorem fresh (atoms) (supported : Supported atoms) :
 GeneralNominalVersionedAllocation231.Fresh (current atoms).state registry focus.identity (packet atoms).bindings := by
 rw [bindings_empty]
 intro key member collision
 have old : key ∈ GeneralNominalAllocation.keys registry focus.identity := member
 exact GeneralNominalCenteredHeadAllocMergeConflict.fresh supported key old collision

theorem prepared (atoms) (good : Good atoms) (supported : Supported atoms) :
 GeneralNominalVersionedCandidates231.Prepared registry (current atoms) focus chosen := by
 refine ⟨source.metadata,⟨?_,?_⟩,[],rfl,?_,?_,uniform,head_models atoms uniform (raw_uniform good)⟩
 · intro index; exact Fin.elim0 index
 · intro output member; cases member
 · exact fresh atoms supported
 · rw [GeneralNominalCenteredHeadAllocMergeConflict.empty_report]
   exact ⟨rfl,rfl,rfl⟩

theorem frame (atoms) (good : Good atoms) (supported : Supported atoms) :
 GeneralNominalVersionedEvidence231.Frame registry (stage atoms).core focus 38 (candidate atoms) :=
 ⟨rfl,rfl,rfl,rfl,List.mem_cons_of_mem _ List.mem_cons_self,
  List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_of_mem _ (List.mem_singleton_self _),
  rfl,rfl,prepared atoms good supported⟩
end Yulang.GeneralRebaseMergeFrame261
