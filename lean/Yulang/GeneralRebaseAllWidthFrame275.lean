import Yulang.GeneralRebaseAllWidthPacket275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralRebaseAllWidthFrame275
open GeneralRebaseAllWidthPlan275
open GeneralRebaseAllWidthPacket275 (packet_holds)
open GeneralRebaseAllWidthRealized275 (successor model_exact)
open GeneralRebaseAllWidthCertificate275 (context)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedPlans231 (head_models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryOptionalInitial229 (registry declaration source)
open GeneralDictionaryVersionedSecondInstall233 (installed effect installed_model)
open GeneralDeclarations GeneralNominalCenters GeneralNominalRecursiveCandidates

theorem raw_sites : successor.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] :=
 GeneralDictionaryVersionedSecondSelected233.raw_sites

theorem centers : successor.core.sites = [rootSite snapshot.seed root] :=
 GeneralDictionaryVersionedSecondSelected233.centers

theorem edges_empty : successor.core.erased.current.edges = [] :=
 GeneralDictionaryVersionedSecondStable233.edges_empty

theorem prepared : Prepared registry context root declaration := by
 have prior : Prepared registry installed.core.erased.current.context root declaration :=
   GeneralDictionaryVersionedSecondSelected233.frame.prepared
 obtain ⟨metadataProof,linked,_,_,_,_,_⟩ := prior
 let canonical := GeneralDictionaryVersionedBothModel233.extended
 have model : Models successor canonical := (model_exact canonical).mpr installed_model
 refine ⟨metadataProof,GeneralNominalRefinements.linked GeneralRebaseAllWidthRefinement275.refines _ linked,packet.bounds,
   located,?_,?_,canonical,head_models (packet_holds canonical model)⟩
 · change GeneralNominalVersionedAllocation231.Fresh context.state registry root.identity packet.bindings
   rw [bindings_exact]
   intro key member _
   apply GeneralNominalVersionedInstallation231.replay_keys_owned retained
   change key ∈ GeneralNominalVersionedAllocation231.keys registry root.identity retained.packet.bindings
   rw [GeneralDictionaryVersionedPoint233.bindings_exact]
   exact member
 · change GeneralNominalRecursiveInspection.Finished (report context declaration [((0 : Fin 8),(0 : Fin 8))])
   rw [report_exact]
   exact ⟨rfl,rfl,rfl⟩

theorem frame : Frame registry successor.core root declaration.id plan := by
 refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_singleton_self _,rfl,located,prepared⟩
 · rw [raw_sites]
   exact List.mem_singleton_self _
 · rw [centers]
   exact List.mem_singleton_self _

theorem singleton_frame (candidate : GeneralNominalCenters.Plan roles) (key : Nat)
 (found : Frame registry successor.core root key candidate) : candidate = plan :=
 GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centers found frame

end Yulang.GeneralRebaseAllWidthFrame275
