import Yulang.GeneralRebaseDepthHalt285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseDepthHaltEvidence285
open GeneralDictionaryOutputDepth252 (snapshot plan root registry roles declaration model context)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseDepthScalar285 (target refreshed fixed_models)
open GeneralRebaseDepthCommit285 (finalPlan ref interp seen located raw_sites center_sites exact_plan classes committed)
open GeneralNominalVersionedEvidence231 (Evidence Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthGroundModels285 (FinalTypeCheck final_check)

theorem final_models (m : Assignment) : Models refreshed m ↔ FinalTypeCheck m :=
 (fixed_models m).trans (final_check m)

theorem final_children : GeneralNominalVersionedFrame231.children finalPlan.packet = [] :=
 (GeneralRebaseNonleafRetarget276.children_eq plan ref interp seen).trans
  GeneralDictionaryOutputDepth252.children_empty

theorem metadata : GeneralNominalRecursiveCandidates.Metadata registry target :=
 GeneralDictionaryRefinedLocations.metadata context target ref interp registry
  GeneralDictionaryOutputDepth252.metadata

theorem final_prepared : Prepared registry target root declaration := by
 obtain ⟨_,link,bounds,before,_,finished,_⟩ := GeneralDictionaryOutputDepth252.prepared
 have sameBounds : bounds = plan.packet.bounds :=
   Option.some.inj (before.symm.trans GeneralDictionaryOutputDepth252.frame.located)
 subst bounds
 have finalValid := (fixed_models model).mpr installed_model
 have holds := (committed.1 model finalValid).1
 refine ⟨metadata,GeneralNominalRefinements.linked ref _ link,finalPlan.packet.bounds,located,?_,?_,
   model,GeneralNominalVersionedPlans231.head_models holds⟩
 · have bindings : finalPlan.packet.bindings = plan.packet.bindings :=
     GeneralRebaseRetarget275.packet_bindings plan ref interp seen
   change GeneralNominalVersionedAllocation231.Fresh target.state registry root.identity finalPlan.packet.bindings
   rw [bindings]
   intro key member _
   exact List.mem_append_right _ member
 · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report (GeneralRebaseRetarget275.retarget plan ref).packet)
   rw [GeneralRebaseRetarget275.report plan ref interp seen]
   exact (GeneralNominalSlotFacts198.finished_report ref.base.embed _).mpr finished

theorem final_frame : Frame registry refreshed.core root 0 finalPlan :=
 ⟨rfl,rfl,rfl,rfl,raw_sites ▸ List.mem_singleton_self _,
   center_sites ▸ List.mem_singleton_self _,List.mem_singleton_self _,rfl,located,final_prepared⟩

theorem final_ready : GeneralNominalCenteredHeadMatEffects.Ready refreshed.core root finalPlan := by
 apply GeneralRebaseRetargetEffects275.ready plan ref interp _
 apply (GeneralNominalVersionedFrameTransport232.ready_iff
    (before := refreshed.core) (after := GeneralDictionaryOutputDepth252.initial.core) ?_).mpr
    GeneralDictionaryOutputDepthInstall252.ready
 intro out
 refine (GeneralNominalVersionedRefresh232.refresh_requests installed target).trans ?_
 exact GeneralNominalVersionedTerminal232.requests_iff GeneralDictionaryOutputDepth252.children_empty

theorem evidence_payload (m : Assignment) (p : Payload) :
    Models refreshed m ∧ Evidence registry refreshed.core m root p ↔
      FinalTypeCheck m ∧ p = .node 0 [] := by
  constructor
  · rintro ⟨held,proof⟩
    refine ⟨(final_models m).mp held,?_⟩
    have reconstructed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr proof
    cases reconstructed with
    | node localCert next =>
      obtain ⟨actual,details⟩ := localCert
      have equal := exact_plan details.frame
      subst actual
      rw [details.children_eq,final_children] at next
      cases next
      exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k []) details.frame.key_eq.symm
  · rintro ⟨checked,rfl⟩
    have actual := (final_models m).mpr checked
    refine ⟨actual,GeneralNominalVersionedEvidence231.evidence_leaf ⟨finalPlan,?_⟩⟩
    exact GeneralNominalVersionedEvidence231.certificate_of_semantics final_frame final_children.symm
      (committed.1 m actual).1 final_ready (classes m actual)

theorem strict_raw_refinement_payload (m : Assignment) (p : Payload) :
    (Models installed m ∧ Evidence registry installed.core m root p) ↔
    (Models refreshed m ∧ Evidence registry refreshed.core m root p) :=
  (GeneralRebaseDepthPayload285.same_assignment_exact m p).trans (evidence_payload m p).symm

end Yulang.GeneralRebaseDepthHaltEvidence285
