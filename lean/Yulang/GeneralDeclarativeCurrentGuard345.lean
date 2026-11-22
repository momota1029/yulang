import Yulang.GeneralDeclarativeCurrentBarrier345
import Yulang.GeneralDeclarativeCurrentProposal345

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeCurrentGuard345
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry declaration)
open GeneralLiveCompoundLeafInstall316 (after after_model)
open GeneralLiveCompoundPostFrames316 (rootPlan root_frame_plan no_root_packet)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCenteredHeadDefaultSchemas (RequestsDeclared)

theorem no_committed : ¬ Committed after rootPlan := by
  intro status
  exact no_root_packet after_model (status.1 _ after_model).1

theorem no_installable {e : Effect roles} (atRoot : e.plan.packet.site.occurrence = root) :
    ¬ Installable registry after e := by
  intro available
  have current : Frame registry after.core root e.plan.packet.declaration.id e.plan := by
    rw [← available.registry_eq,← available.snapshot_eq,← atRoot]
    exact e.frame
  obtain ⟨model,fit,packet,_⟩ := available.common
  exact no_root_packet fit (by simpa only [root_frame_plan current] using packet)

theorem ready_still_unavailable :
    RequestsDeclared after.core root rootPlan ∧ Ready after.core root rootPlan ∧
    (∀ e : Effect roles, e.plan.packet.site.occurrence = root → ¬ Installable registry after e) := by
  exact ⟨GeneralDeclarativeCurrentBarrier345.ready.1,
    GeneralDeclarativeCurrentBarrier345.ready.2,fun _ atRoot => no_installable atRoot⟩

end Yulang.GeneralDeclarativeCurrentGuard345
