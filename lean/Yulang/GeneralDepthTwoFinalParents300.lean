import Yulang.GeneralDepthTwoSecondInstall300
import Yulang.GeneralDepthTwoFrameCarry300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralDepthTwoFinalParents300
open GeneralGeneratedNestedSource299 (root)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final final_requests models)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedInstallation231 (replayPlan reserved atoms allocated)
open GeneralNominalVersionedTransport231 (extendedPlan)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedFrame231 (children)
open GeneralRebaseDisplayFrame276 (classes_empty)

abbrev oldRoot := replayPlan GeneralDepthTwoRootPlan300.plan
abbrev middleCommit := GeneralDepthTwoMiddleContext300.plan
abbrev rootNow := extendedPlan (reserved middleCommit.packet) (atoms middleCommit.packet)
  (allocated middleCommit.packet) oldRoot
abbrev middleNow := replayPlan middleCommit

theorem owns_previous_root :
    GeneralNominalVersionedAllocation231.keys compiled root.identity oldRoot.packet.bindings ⊆
      oldRoot.packet.context.state.allocated ++ allocated middleCommit.packet := by
  intro k member
  apply List.mem_append_left
  change k ∈ allocated GeneralDepthTwoRootPlan300.plan.packet
  have binding : oldRoot.packet.bindings = GeneralDepthTwoRootPlan300.plan.packet.bindings :=
    GeneralNominalVersionedTransport231.packet_bindings ..
  rw [binding] at member
  exact member

theorem new_atoms (m : Assignment) (valid : Models final m) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m (atoms middleCommit.packet) :=
  ((GeneralDictionaryOrdinaryTransport.models_extended ..).mp valid.1.1).2

theorem root_holds (m : Assignment) (valid : Models final m) : Holds rootNow m := by
  have atFirst := (models m).mp valid
  have old : Holds oldRoot m := GeneralNominalVersionedInstalledEvidence233.replay_holds atFirst
  exact (GeneralNominalVersionedTransport231.holds_iff ..).mpr ⟨old,new_atoms m valid⟩

theorem root_frame (m : Assignment) (valid : Models final m) :
    Frame compiled final.core root 1 rootNow := by
  have atFirst := (models m).mp valid
  have old : Frame compiled after.core root 1 oldRoot :=
    GeneralNominalVersionedInstalledEvidence233.frame rfl atFirst
  have rebuilt := GeneralDepthTwoFrameCarry300.frame_carried (reserved middleCommit.packet)
    (atoms middleCommit.packet) (allocated middleCommit.packet) compiled after.core root 1 oldRoot
    old owns_previous_root m (root_holds m valid)
  exact GeneralNominalVersionedFrameTransport232.frame_forward
    (before := GeneralNominalCenteredSteps.refresh after.core
      (GeneralDictionaryOrdinaryTransport.extend after.core.erased.current.context
        (reserved middleCommit.packet) (atoms middleCommit.packet) (allocated middleCommit.packet)))
    (after := final.core) rfl
    (fun _ present => List.mem_append_left _ present)
    (fun _ present => List.mem_append_left _ present) rebuilt

theorem root_children : children rootNow.packet = [middle] :=
  (GeneralNominalVersionedTransport231.children_eq ..).trans
    ((GeneralNominalVersionedInstallation231.replay_children _).trans
      GeneralGeneratedNestedPredictions299.parent_children)

theorem root_instance (m : Assignment) (valid : Models final m) :
    Instance compiled final.core m root 1 [middle] := by
  refine ⟨rootNow,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (root_frame m valid) root_children.symm (root_holds m valid) ?_ ?_⟩
  · intro output member
    rw [final_requests] at member
    cases member
  · exact classes_empty (final_requests root) rootNow m

theorem middle_frame (m : Assignment) (valid : Models final m) :
    Frame compiled final.core middle 1 middleNow :=
  GeneralNominalVersionedInstalledEvidence233.frame rfl valid

theorem middle_holds (m : Assignment) (valid : Models final m) : Holds middleNow m :=
  GeneralNominalVersionedInstalledEvidence233.replay_holds valid

theorem middle_children : children middleNow.packet = [terminal] :=
  (GeneralNominalVersionedInstallation231.replay_children _).trans GeneralDepthTwoMiddleContext300.same_children

theorem middle_instance (m : Assignment) (valid : Models final m) :
    Instance compiled final.core m middle 1 [terminal] := by
  refine ⟨middleNow,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (middle_frame m valid) middle_children.symm (middle_holds m valid) ?_ ?_⟩
  · intro output member
    rw [final_requests] at member
    cases member
  · exact classes_empty (final_requests middle) middleNow m

end Yulang.GeneralDepthTwoFinalParents300
