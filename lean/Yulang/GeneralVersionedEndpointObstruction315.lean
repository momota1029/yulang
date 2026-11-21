import Yulang.GeneralVersionedEndpointObstructionSelect315
import Yulang.GeneralVersionedChildDemandCut315

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 18000000
/-! The C314 sufficient endpoint producer is false on an actual reached,
stable, locally selected non-replay case, despite the existence of its
current centered head. Its child is rejected, so this is not a
counterexample to the original recursive dictionary theorem. -/
namespace Yulang.GeneralVersionedEndpointObstruction315
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration checked compiled_registry)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperRoot307 (plan frame_plan)
open GeneralMixedCompoundUpperHalt307 (stable)
open GeneralMixedCompoundUpperChild307 (reachable no_evidence)
open GeneralVersionedEndpointObstructionHead315 (valid)
open GeneralVersionedEndpointObstructionSelect315 (selected)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedRecursiveBridge310 (PendingCase CurrentCandidate ReplayFrame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalCommonBridge (Assignment)

theorem checked_source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked sourceRegistry :=
  ⟨rfl,checked⟩

theorem no_replay : ¬ ReplayFrame sourceRegistry upperState root declaration.id [childSite.occurrence] := by
  rintro ⟨old,member,rs,ats,allocated,framed,order⟩
  have certified := GeneralVersionedHistoryEvidence310.recorded_extension checked_source reachable member rs ats
    allocated framed order valid
  have same := frame_plan framed
  rw [same] at certified
  exact GeneralMixedCompoundUpperObstruction307.no_current_packet extended valid certified.packet

theorem pending : PendingCase sourceRegistry upperState root root declaration.id [childSite.occurrence] :=
  ⟨checked_source,reachable,Or.inl rfl,stable,selected,⟨extended,valid⟩,no_replay⟩

theorem no_residual {e : GeneralNominalVersionedJournal232.Effect roles}
    (candidate : CurrentCandidate sourceRegistry upperState root declaration.id [childSite.occurrence] e) :
    ¬ ∃ m, Residual upperState e m := by
  rintro ⟨m,rest⟩
  have frame : GeneralNominalVersionedEvidence231.Frame (Compiled sourceRegistry) upperState.core
      e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    candidate.1 ▸ candidate.2.1 ▸ e.frame
  have held := (GeneralNominalVersionedChildClosure237.source_holds_iff upperState e.plan m reachable frame rest.1).mpr
    ⟨rest.2.1,rest.2.2.1,rest.2.2.2.1,rest.2.2.2.2.1⟩
  rw [candidate.2.2.1] at frame
  have same := frame_plan frame
  rw [same] at held
  exact GeneralMixedCompoundUpperObstruction307.no_current_packet m rest.1 held

theorem old_endpoint_false : ¬ GeneralVersionedRecursiveCut314.EndpointReads roles := by
  intro claim
  obtain ⟨e,g,s,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect checked_source reachable selected
  have candidate : CurrentCandidate sourceRegistry upperState root declaration.id [childSite.occurrence] e :=
    ⟨g,s,o,k,c⟩
  have readback := claim _ _ _ _ _ _ _ pending candidate
  have picked : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry upperState e.plan.packet.site.occurrence
      (.selected e.plan.packet.declaration.id [childSite.occurrence]) := by
    rw [o,k]; exact selected
  have exactFrame := e.frame
  rw [g,s] at exactFrame
  exact no_residual candidate (GeneralVersionedRemainingWrites314.joint checked_source reachable picked g s ⟨extended,valid⟩
    (GeneralVersionedEndpointReduction314.reused checked_source reachable picked exactFrame readback))

theorem no_child_demand (m : Assignment) :
    ¬ GeneralVersionedChildDemandCut315.ChildDemand sourceRegistry upperState m [childSite.occurrence] := by
  rintro ⟨_,_,ordered⟩
  cases ordered with
  | cons one _ => exact no_evidence m _ one

theorem no_counterexample_to_node :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry upperState root :=
  GeneralMixedCompoundUpperOutcome307.evidenceAt

end Yulang.GeneralVersionedEndpointObstruction315
