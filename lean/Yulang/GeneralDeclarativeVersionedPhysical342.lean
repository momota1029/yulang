import Yulang.GeneralDeclarativeVersionedRetarget342
import Yulang.GeneralWherePhysicalEvidence319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralDeclarativeVersionedPhysical342
open GeneralWherePhysicalCurrentRead319 (plan packet query nominal0 locate)
open GeneralWherePhysicalCommit319 (final newChild physical_mixed_run both_in_history child_changed produced emission)
open GeneralWherePhysicalActive319 (active ctx refines)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWhereOriginSingleSource318 (oldPlan sourceRegistry registry declaration)
open GeneralWhereOriginSingleCells318 (loNow hi oldChild sig)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereVersionCompiler317 (children)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralRebaseRetarget275 (retarget Observed)
open GeneralDeclarativeVersionedRetarget342 (same holds)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCenteredHeadOutputs (requests)

noncomputable abbrev current := retarget plan (after := ctx) refines

theorem observed : Observed plan := by
  unfold Observed
  rw [show GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
    plan.packet.declaration = [.nominal 0 [.variables [0],.variables [1]]] from query]
  exact .cons (.point nominal0 rfl rfl (.cons .variables (.cons .variables .nil))) .nil

theorem transported : GeneralNominalCenteredHeadMatPlanData.Same current plan :=
  same (after := ctx) plan refines rfl observed

theorem recorded_version : plan ∈ final.versionedWhere := GeneralWherePhysicalEvidence319.recorded

theorem holds_now (m : Assignment) (valid : Models final m) : Holds current m :=
  holds (after := ctx) plan refines rfl observed m valid.1.1.1 (valid.2 plan recorded_version).1

theorem actual_children : children current = [newChild.occurrence] :=
  (GeneralWhereVersionRecompile317.children_eq transported).trans GeneralWherePhysicalEvidence319.compiled_child

theorem unchanged_targets (outputs : List GeneralSourceState.Output) :
    GeneralDeclarativeStoppedOrder339.compileRequests current outputs =
    GeneralDeclarativeStoppedOrder339.compileRequests plan outputs :=
  GeneralDeclarativeStoppedRetarget341.ordered_rows_same (after := ctx) plan refines rfl observed outputs

theorem new_registered : newChild ∈ final.mixed.core.sites := by
  change newChild ∈ updated.mixed.core.sites ++ GeneralWhereVersionInstall317.emitted plan
  rw [emission]
  exact List.mem_append_right _ List.mem_cons_self

theorem old_registered : oldChild ∈ final.mixed.core.sites := by
  change oldChild ∈ updated.mixed.core.sites ++ GeneralWhereVersionInstall317.emitted plan
  rw [GeneralWherePhysicalCurrentPick319.centers]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The historical and current child share a source occurrence ID, but
are distinct raw occurrences and have different lower endpoint
addresses. This is exactly why an identity-only lookup is insufficient. -/
theorem same_id_not_occurrence :
    oldChild.occurrence.identity = newChild.occurrence.identity ∧ oldChild.occurrence ≠ newChild.occurrence :=
  ⟨GeneralWhereOriginSingleCells318.same_child_identity.trans
    (congrArg (fun x : GeneralNominalCenters.Site roles => x.occurrence.identity)
      (GeneralWhereVersionCurrentCert317.child_site_eq GeneralWherePhysicalCurrentRead319.same
        GeneralLiveCompoundRegistry316.otherChild sig)),child_changed⟩

theorem old_not_current :
    oldChild ∈ final.mixed.core.sites ∧ newChild ∈ final.mixed.core.sites ∧
    oldChild.occurrence ∉ children current ∧
    ∀ d ∈ children current, Generated final.mixed.core.erased.current root d := by
  rw [actual_children]
  refine ⟨old_registered,new_registered,?_,?_⟩
  · intro old
    exact child_changed (List.mem_singleton.mp old)
  · intro d old
    cases List.mem_singleton.mp old
    exact produced

theorem actual_model_packet (m : Assignment) (valid : Models final m) :
    Holds current m ∧ GeneralNominalVersionedEffects231.ClassEffects final.mixed.core root current m := by
  have old : GeneralNominalVersionedEffects231.ClassEffects final.mixed.core root plan m := by
    change GeneralNominalVersionedEffects231.ClassEffects final.mixed.core plan.packet.site.occurrence plan m
    exact (valid.2 plan recorded_version).2
  refine ⟨holds_now m valid,?_⟩
  exact GeneralRebaseRetargetEffects275.class_effects (after := ctx) (root := root)
    plan refines rfl final.mixed.core observed m old

end Yulang.GeneralDeclarativeVersionedPhysical342
