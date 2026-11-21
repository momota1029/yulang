import Yulang.GeneralLiveCompoundPostRootSelect316
import Yulang.GeneralVersionedRevisitCut315

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 44000000
/-! Actual non-vacuous failure of the current Lean mixed/source
EvidenceNode statement. The child is generated, installed, stable and
certified in the queried model. Nothing here changes source acceptance,
claims a Rust execution, or uses termination of arbitrary source programs. -/
namespace Yulang.GeneralLiveCompoundCounterexample316
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf boundary_checked)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundLeafInstall316 (after after_model reachable)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundPostFrames316 (leaf_evidence no_root_evidence no_root_packet root_frame_plan)
open GeneralLiveCompoundPostRootSelect316 (selected)
open GeneralLiveCompoundStable316 (stable leaf_stable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedRecursiveBridge310 (ReplayFrame PendingCase CurrentCandidate)
open GeneralVersionedChildDemandCut315 (ChildDemand)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalVersionedEvidence231 (Evidence)

abbrev dictionaries : List GeneralDictionaryReadback.Payload := [.node leaf.id []]

theorem child_ordered : All₂ (Evidence registry after.core w) [child] dictionaries :=
  .cons (leaf_evidence after_model) .nil

theorem ordered : ChildDemand sourceRegistry after w [child] :=
  ⟨dictionaries,after_model,child_ordered⟩

theorem not_at : ¬ B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry after root := by
  intro claimed
  exact no_root_evidence after_model _
    (claimed w after_model root declaration.id [child] dictionaries
      (Or.inl rfl) stable
      (fun kid seen => (List.mem_singleton.mp seen).symm ▸ leaf_stable)
      selected child_ordered)

theorem not_evidenceNode : ¬ B4SkeletonV8.EvidenceNode (boundary roles) :=
  fun soundness => not_at (soundness sourceRegistry boundary_checked after root reachable)

theorem no_replay : ¬ ReplayFrame sourceRegistry after root declaration.id [child] := by
  rintro ⟨old,inHistory,registryEq,slots,allocated,framed,order⟩
  have cert := GeneralVersionedHistoryEvidence310.recorded_extension boundary_checked reachable inHistory
    registryEq slots allocated framed order after_model
  exact no_root_packet after_model (by simpa only [root_frame_plan framed] using cert.packet)

theorem pending : PendingCase sourceRegistry after root root declaration.id [child] :=
  ⟨boundary_checked,reachable,Or.inl rfl,stable,selected,⟨w,after_model⟩,no_replay⟩

theorem not_revisit_rhs : ¬ GeneralVersionedRevisitCut315.RevisitRhs roles := by
  intro claimed
  obtain ⟨e,g,s,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect boundary_checked reachable selected
  have candidate : CurrentCandidate sourceRegistry after root declaration.id [child] e := ⟨g,s,o,k,c⟩
  have prior : GeneralLiveCompoundRoot316.plan ∈ after.plans :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have same : GeneralLiveCompoundRoot316.plan.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity := by
    rw [o]; rfl
  have input := claimed sourceRegistry after root root declaration.id [child] e pending candidate w ordered _ prior same
  have picked : Local sourceRegistry after e.plan.packet.site.occurrence
      (.selected e.plan.packet.declaration.id [child]) := by rw [o,k]; exact selected
  obtain ⟨m,rest⟩ := (GeneralVersionedEndpointWholeRhs315.joint_with_rhs boundary_checked reachable picked g s prior same).mpr input
  have frame := e.frame
  rw [g,s,o] at frame
  have packet := (GeneralNominalVersionedChildClosure237.source_holds_iff after e.plan m reachable
    (g ▸ s ▸ e.frame) rest.1).mpr ⟨rest.2.1,rest.2.2.1,rest.2.2.2.1,rest.2.2.2.2.1⟩
  exact no_root_packet rest.1 (by simpa only [root_frame_plan frame] using packet)

end Yulang.GeneralLiveCompoundCounterexample316
