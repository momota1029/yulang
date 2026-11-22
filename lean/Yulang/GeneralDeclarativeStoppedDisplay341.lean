import Yulang.GeneralDeclarativeStoppedDisplayModern341
import Yulang.GeneralDeclarativeStoppedLeafFixture340
import Yulang.GeneralDeclarativeStoppedLockstep341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 15600000
namespace Yulang.GeneralDeclarativeStoppedDisplay341
open GeneralNominalExamples (registry interpretation registry_checked displayRoot displayChild model)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (after generated)
open GeneralRebaseDisplaySelection276 (parent child parent_frame child_frame picked_parent picked_child)
open GeneralRebaseDisplayStable276 (halted committed_parent committed_child)
open GeneralRebaseDisplaySafety276 (after_model)
open GeneralRebaseDisplayEndpoint276 (generates_only)
open GeneralRebaseDisplayExecutor276 (run raw run_exact)
open GeneralDeclarativeStoppedLeafFixture340 (no_peer_choice not_journaled)
open GeneralNominalVersionedMixedBoundary234 (boundary Local)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedMixedFrameSelection235 (selected_identifies)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarativeStoppedSelected340 (FitFrame)
open GeneralStoppedDisplayProjection335 (parentDemand childDemand)
open GeneralStoppedDisplayCut335 (reminted closed)
open GeneralStoppedDisplayExtended335 (expanded augmented conservative placement)
open GeneralStoppedDisplayGuard335 (waiting covered parent_declared)
open GeneralDeclarativeTaggedDictionary340 (Rule dictionary_sound)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)
open GeneralDeclarativeFootprint321 (stateNames)

theorem parent_choice :
    GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current parent.packet := by
  intro prior there same
  change prior ∈ [GeneralNominalNonleafPlan193.plan.packet] at there
  cases List.mem_singleton.mp there
  rfl

theorem parent_fit : FitFrame (s := after) displayRoot parent := by
  obtain ⟨packet,outputs⟩ := committed_parent.1 model after_model
  exact ⟨parent_choice,model,after_model,packet,outputs⟩

theorem child_fit : FitFrame (s := after) displayChild child := by
  obtain ⟨packet,outputs⟩ := committed_child.1 model after_model
  exact ⟨no_peer_choice,model,after_model,packet,outputs⟩

/-- Independently fill both current packets at the real two-occurrence
compiled stop, not by guessing from successful reported key numbers. -/
theorem all_current {a}
    (live : Generated after.core.erased.current displayRoot a)
    (selected : Local registry after a (.selected key kids)) :
    ∃ plan, Frame registry after.core a key plan ∧ FitFrame (s := after) a plan := by
  rcases generates_only live with rfl|rfl
  · obtain ⟨keySame,_⟩ := selected_identifies selected parent_frame
    cases keySame
    exact ⟨_,parent_frame,parent_fit⟩
  · obtain ⟨keySame,_⟩ := selected_identifies selected child_frame
    cases keySame
    exact ⟨_,child_frame,child_fit⟩

theorem classified :
    B4TargetV8.Classify (boundary roles) registry after displayRoot (.selected (.node 1 [.node 3 []])) :=
  .selected picked_parent (.cons (.selected picked_child .nil) .nil)

theorem modern (done : Nat → Prop) :
    Classify (Rule (augmented done) [] registry interpretation waiting) parentDemand (.selected (.node 1 [.node 3 []])) :=
  ⟨.selected 1 [.selected 3 []],
    .selected (.whole (GeneralDeclarativeStoppedDisplayModern341.parent done))
      (.cons (.selected (.whole (GeneralDeclarativeStoppedDisplayModern341.child done)) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

/-- Actual compiled solver success, projected to the latest C340
witness judgment. Reminted endpoints are explicit; preserve all old
ordinary names, never require raw assignments to agree at fresh ones. -/
theorem actual_success (done : Nat → Prop) (finished : run key = some (phase,payload)) :
    B4TargetV8.Reachable (boundary roles) registry displayRoot (raw phase) ∧
    (∀ next, ¬ Step registry displayRoot (raw phase) next) ∧
    B4TargetV8.Classify (boundary roles) registry (raw phase) displayRoot (.selected payload) ∧
    Classify (Rule (augmented done) [] registry interpretation waiting) parentDemand (.selected payload) ∧
    GeneralStoppedPlacement335.SameDemand expanded childDemand reminted ∧
    ∀ m, Models (raw phase) m →
      ∃ n, Models (raw phase) n ∧ (∀ v ∈ stateNames closed, n v = m v) ∧
        Evidence registry (raw phase).core n displayRoot payload ∧
        GeneralDeclarativeExactDictionary337.Evidence registry interpretation n parentDemand payload := by
  obtain ⟨_,rfl,rfl⟩ := (run_exact key phase payload).mp finished
  have stable := GeneralRebaseDisplayStep276.reachable
  have now := modern done
  refine ⟨stable,halted,classified,now,placement,?_⟩
  intro m fit
  obtain ⟨n,ordinary,keeps⟩ := (conservative m).mp fit
  have sameRaw := (conservative n).mpr ⟨n,ordinary,fun _ _ => rfl⟩
  exact ⟨n,sameRaw,keeps,GeneralRebaseDisplayEvidence276.real_nonleaf n sameRaw,
    dictionary_sound registry_checked covered parent_declared now ⟨ordinary,fun _ h => False.elim (List.not_mem_nil h)⟩⟩

end Yulang.GeneralDeclarativeStoppedDisplay341
