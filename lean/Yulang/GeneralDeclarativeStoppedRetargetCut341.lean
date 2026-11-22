import Yulang.GeneralDeclarativeStoppedHistory341
import Yulang.GeneralDeclarativeStoppedDepth341
import Yulang.GeneralDeclarativeStoppedObstruction341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32500
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeStoppedRetargetCut341
open GeneralDeclarativeStoppedHistory341 (derive_current)
open GeneralDeclarativeStoppedRetarget341 (recorded_semantics ordered_rows_same)
open GeneralDeclarativeStoppedObstruction341 (packet_impossible)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalRefinements (Refines)
open GeneralRebaseRetarget275 (Observed retarget)

section C316
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralLiveCompoundRegistry316 (registry)
open GeneralLiveCompoundLeafInstall316 (after reachable after_model)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralNominalVersionedJournal232 (Effect)

theorem no_retained_transport {old : Effect GeneralDictionaryJournalRefinement228Source.roles}
    (retained : old ∈ after.effects)
    (ref : Refines old.plan.packet.context.state after.core.erased.current.context.state)
    (interp : after.core.erased.current.context.interpretation = old.plan.packet.context.interpretation)
    (seen : Observed old.plan) :
    ¬ Frame registry after.core root key (retarget old.plan ref) := by
  intro new
  have raised := recorded_semantics old.plan ref interp seen reachable retained rfl rfl w after_model
  exact packet_impossible new after_model raised.1

end C316

section C285
open GeneralDictionaryOutputDepth252 (sourceRegistry root roles)
open GeneralDictionaryOutputDepthInstall252 (effect)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralRebaseDepthCommit285 (ref interp seen finalPlan)
open GeneralRebaseDepthHaltSelection285 (selected)
open GeneralDeclarativeStoppedRetarget340 (reach)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDeclarativeStoppedSelected340 (FitFrame)
open GeneralDeclarativeStoppedOrder339 (compileRequests)
open GeneralNominalCenteredHeadOutputs (requests)

theorem retained285 : effect ∈ refreshed.effects := List.mem_cons_self

theorem unique285 : ∀ a ∈ (registry sourceRegistry).declarations,
    ∀ b ∈ (registry sourceRegistry).declarations, a.role = b.role → a.id = b.id := by
  intro a inA b inB _
  rw [List.mem_singleton.mp inA,List.mem_singleton.mp inB]

theorem fit_from_history285 {m} (valid : Models refreshed m) :
    ∃ plan, Frame (registry sourceRegistry) refreshed.core root 0 plan ∧
      FitFrame (s := refreshed) root plan := by
  have checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked sourceRegistry :=
    ⟨rfl,GeneralDictionaryOutputDepth252.source_checked⟩
  exact derive_current checked reach retained285 ref interp seen selected unique285 m valid

theorem unchanged_order285 :
    compileRequests finalPlan (requests refreshed.core root) =
      compileRequests GeneralDictionaryOutputDepth252.plan (requests refreshed.core root) :=
  by
    change compileRequests (retarget GeneralDictionaryOutputDepth252.plan GeneralRebaseDepthCommit285.ref)
      (requests refreshed.core root) = _
    exact ordered_rows_same GeneralDictionaryOutputDepth252.plan GeneralRebaseDepthCommit285.ref interp seen _

end C285
end Yulang.GeneralDeclarativeStoppedRetargetCut341
