import Yulang.GeneralDeclarativeStoppedLeaf340
import Yulang.GeneralStoppedDisplayHistory335
import Yulang.GeneralRebaseDisplayStep276
import Yulang.GeneralNominalVersionedMixedInstallRequests235

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeclarativeStoppedLeafFixture340
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot displayChild model)
open GeneralRebaseDisplayFrame276 (after before generated no_new_request classes_empty)
open GeneralRebaseDisplayChild276 (plan no_children holds emitted_empty)
open GeneralRebaseDisplaySelection276 (safe child_frame unique_child)
open GeneralRebaseDisplayEvidence276 (ready)
open GeneralRebaseDisplaySafety276 (after_model semantic)
open GeneralRebaseDisplayStable276 (halted framed_child)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedCandidates231 (Unique)
open GeneralNominalSaturationState (Alias)
open GeneralNominalVersionedCycles232 (Safe)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralDeclarativeStoppedLeaf340 (committed current_outputs same_model_leaf)
open GeneralNominalCommonBridge (Assignment)

noncomputable def proposed : Effect roles :=
  ⟨registry,after.core,plan,child_frame,no_children.symm ▸ unique_child,ready plan⟩

theorem empty_aliases :
    after.core.erased.current.aliases = [] := rfl

theorem identity_only (edge : Alias after.core.erased.current x y) : x = y := by
  induction edge with
  | refl => rfl
  | edge linked => rw [empty_aliases] at linked; cases linked
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem no_peer_choice :
    GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current plan.packet := by
  intro prior onRecord same
  change prior ∈ [GeneralNominalNonleafPlan193.plan.packet] at onRecord
  cases List.mem_singleton.mp onRecord
  have identity := identity_only same
  have distinct : displayChild.identity ≠ displayRoot.identity := by decide +kernel
  exact False.elim (distinct identity)

theorem positions : Safe after plan := by
  refine ⟨by decide +kernel,?_⟩
  intro entry _
  exact semantic after_model entry.1

theorem can_install : Installable registry after proposed := by
  refine ⟨rfl,rfl,safe (Or.inr rfl),?_,?_,no_peer_choice,positions,?_,?_⟩
  · exact GeneralNominalVersionedMixedCache233.install_cache (effect := GeneralRebaseDisplayFrame276.effect) rfl
      GeneralRebaseDisplayStep276.installable.cache
  · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
    rw [emitted_empty]
  · intro other _ located
    rw [framed_child located]
    exact positions
  · refine ⟨model,(GeneralNominalVersionedMixedInstallRequests235.no_outputs_installation_iff
        (state := after) (effect := proposed) rfl ?_).mpr ⟨after_model,holds model after_model,?_⟩⟩
    · intro child encountered
      change child ∈ GeneralNominalVersionedFrame231.children plan.packet at encountered
      rw [no_children] at encountered
      cases encountered
    · exact classes_empty (no_new_request displayChild) plan model

theorem not_journaled :
    ∀ e ∈ after.effects, e.plan.packet.site.occurrence ≠ proposed.plan.packet.site.occurrence :=
  GeneralStoppedDisplayHistory335.selected_not_installed.2

/-- Truly reached and halted leaf, its source plan is installable but
not stored as an effect. Its current request list happens to be empty. -/
theorem actual_leaf (m : Assignment) (fit : Models after m) :
    Evidence registry after.core m displayChild (.node 3 []) ∧
    GeneralDeclarativeStoppedOrder339.compileRequests plan
      (GeneralNominalCenteredHeadOutputs.requests after.core displayChild) = some [] := by
  refine ⟨same_model_leaf halted generated can_install no_children m fit,?_⟩
  rw [no_new_request]
  rfl

theorem reached_and_stopped :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedBoundary234.boundary roles) registry displayRoot after ∧
      (∀ next, ¬ GeneralNominalVersionedMixedKernel234.Step registry displayRoot after next) :=
  ⟨GeneralRebaseDisplayStep276.reachable,halted⟩

end Yulang.GeneralDeclarativeStoppedLeafFixture340
