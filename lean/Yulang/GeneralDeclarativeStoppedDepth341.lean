import Yulang.GeneralDeclarativeStoppedLockstep341
import Yulang.GeneralDeclarativeStoppedRetarget340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralDeclarativeStoppedDepth341
open GeneralDictionaryOutputDepth252 (sourceRegistry roles root model source_checked)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralRebaseDepthCommit285 (finalPlan classes committed)
open GeneralRebaseDepthHalt285 (halted)
open GeneralRebaseDepthHaltEvidence285 (final_frame final_children)
open GeneralRebaseDepthHaltSelection285 (selected after_model)
open GeneralDeclarativeStoppedRetarget340 (reach choose_prior row exact_requests exact_packet current_plan_not_retained)
open GeneralDeclarativeStoppedSelected340 (FitFrame)
open GeneralDeclarativeStoppedFold340 (Produces dictionary)
open GeneralDeclarativeStoppedLockstep341 (Terminal)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary local_iff)
open GeneralNominalVersionedMixedFrameSelection235 (selected_identifies)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedMixedTrace235 (generated_registered reachable)

theorem only_root {a : GeneralSourceDictionaries.Occurrence roles}
    (generated : Generated refreshed.core.erased.current root a) : a = root := by
  obtain ⟨site,whereHeld,same⟩ := generated_registered (reachable reach).1 generated
  rw [GeneralRebaseDepthCommit285.raw_sites] at whereHeld
  cases List.mem_singleton.mp whereHeld
  exact same.symm

theorem fit_current : FitFrame (s := refreshed) root finalPlan :=
  ⟨choose_prior,model,after_model,(committed.1 model after_model).1,classes model after_model⟩

theorem producer : Produces sourceRegistry refreshed root := by
  intro a generated key kids picked
  cases only_root generated
  obtain ⟨same,_⟩ := selected_identifies (local_iff.mp picked) final_frame
  cases same
  exact ⟨finalPlan,final_frame,fit_current⟩

theorem terminal : Terminal sourceRegistry refreshed root :=
  ⟨⟨rfl,source_checked⟩,reach,halted,producer⟩

theorem classification :
    B4TargetV8.Classify (boundary roles) sourceRegistry refreshed root (.selected (.node 0 [])) :=
  .selected selected .nil

theorem every_model (m) (fit : Models refreshed m) :
    GeneralNominalVersionedEvidence231.Evidence
      (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) refreshed.core m root (.node 0 []) :=
  dictionary terminal.checked terminal.path terminal.stopped terminal.supports fit classification

end Yulang.GeneralDeclarativeStoppedDepth341
