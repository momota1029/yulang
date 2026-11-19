import Yulang.GeneralRebaseCompiledChildFresh277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9200000
namespace Yulang.GeneralRebaseCompiledEvidence277
open GeneralNominalExamples (registry state displayRoot displayChild intDisplay model)
open GeneralDeclarationExamples (roles)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralRebaseDisplayFrame276 (before classes_empty)
open GeneralRebaseCompiledDisplay277 (compiled after effect parent)
open GeneralRebaseCompiledInstall277 (raw_sites_eq center_sites_eq no_new_request models)
open GeneralRebaseCompiledChild277 (context packet plan report_exact no_children holds)
open GeneralRebaseCompiledChildFresh277 (child_fresh)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence Frame)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalCenters

theorem center_sites : after.core.sites = [rootSite (state true).seed displayRoot,centerSite] :=
 center_sites_eq.trans GeneralRebaseDisplayEvidence276.center_sites

theorem raw_sites : after.core.erased.current.sites =
 [GeneralNominalDemandMerging.pointSite displayRoot,centerSite.observed] :=
 raw_sites_eq.trans GeneralRebaseDisplayEvidence276.raw_sites

theorem prepared (m : Assignment) (valid : Models after m) : Prepared compiled context displayChild intDisplay := by
 have linked : GeneralNominalState.Linked context.state displayChild.demand := by
   constructor
   · intro i
     change 1 ∈ GeneralNominalState.sources context.state ∧ 1 ∈ GeneralNominalState.sources context.state
     exact ⟨GeneralNominalAllocationSupport.slot_source context.state (1 : Fin 2),GeneralNominalAllocationSupport.slot_source context.state (1 : Fin 2)⟩
   · intro output member
     cases member
 refine ⟨GeneralNominalNonleafLocal193.prepared.1,linked,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,m,?_⟩
 · change GeneralNominalVersionedAllocation231.Fresh context.state compiled displayChild.identity packet.bindings
   exact child_fresh
 · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report packet)
   rw [report_exact]
   exact ⟨rfl,rfl,rfl⟩
 · change GeneralNominalVersionedCandidates231.HeadModels packet.registry packet.context packet.site.occurrence packet.declaration packet.bounds m
   apply (GeneralNominalVersionedCandidates231.headModels_packet_iff packet m).mpr
   exact GeneralNominalVersionedPlans231.head_models (plan := plan) (holds m valid)

theorem child_frame (m : Assignment) (valid : Models after m) :
 Frame compiled after.core displayChild 3 plan := by
 refine ⟨rfl,rfl,rfl,rfl,?_,?_,(by exact List.mem_cons_self ..),rfl,rfl,prepared m valid⟩
 · rw [raw_sites]
   simp
 · rw [center_sites]
   simp

theorem ready {focus : GeneralSourceDictionaries.Occurrence roles} (p : Plan roles) :
 GeneralNominalCenteredHeadMatEffects.Ready after.core focus p := by
 intro output recorded
 rw [no_new_request focus] at recorded
 cases recorded

theorem child_evidence (m : Assignment) (valid : Models after m) :
 Evidence compiled after.core m displayChild (.node 3 []) :=
 GeneralNominalVersionedEvidence231.evidence_leaf
   ⟨plan,GeneralNominalVersionedEvidence231.certificate_of_semantics (child_frame m valid)
      no_children.symm (holds m valid) (ready plan) (classes_empty (no_new_request displayChild) plan m)⟩

theorem parent_instance (m : Assignment) (valid : Models after m) :
 GeneralNominalVersionedEvidence231.Instance compiled after.core m displayRoot 1 [displayChild] := by
 let p := replayPlan parent
 refine ⟨p,GeneralNominalVersionedEvidence231.certificate_of_semantics
   (GeneralNominalVersionedInstalledEvidence233.frame rfl valid) ?_
   (GeneralNominalVersionedInstalledEvidence233.replay_holds valid) (ready p)
   (classes_empty (no_new_request displayRoot) p m)⟩
 exact ((GeneralNominalVersionedInstallation231.replay_children _).trans GeneralRebaseCompiledDisplay277.children).symm

theorem real_nonleaf (m : Assignment) (valid : Models after m) :
 Evidence compiled after.core m displayRoot (.node 1 [.node 3 []]) :=
 GeneralNominalVersionedEvidence231.evidence_node (parent_instance m valid)
  (.cons (child_evidence m valid) .nil)

theorem source_nonleaf (m : Assignment) (valid : GeneralNominalState.Models (state true) m) :
 Evidence compiled after.core m displayRoot (.node 1 [.node 3 []]) :=
 real_nonleaf m ((models m).mpr ((GeneralRebaseDisplayExecutor276.model_exact .source m).mpr valid))

/-- Evidence at the real source adapter (the original registry remains the input). -/
theorem adapter_evidence (m : Assignment) (valid : Models after m) :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Evidence
      registry after m displayRoot (.node 1 [.node 3 []]) := real_nonleaf m valid

end Yulang.GeneralRebaseCompiledEvidence277
