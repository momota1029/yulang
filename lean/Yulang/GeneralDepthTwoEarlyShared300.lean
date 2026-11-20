import Yulang.GeneralDepthTwoFinalHalt300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralDepthTwoEarlyShared300
open GeneralGeneratedNestedSource299 (root model initial)
open GeneralGeneratedNestedPredictions299 (compiled)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralDepthTwoFinalSeparators300 (patch patched all_known equality_names free)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)

theorem headless_transfer (s : State roles)
    (transfer : ∀ m, Models final m → Models s m)
    (known : ∀ id, id ≤ 2 → GeneralNominalState.Known s.core.erased.current.context.state id) :
    HeadlessUnknown s := by
  refine ⟨patch (fun _ => .top),transfer _ (patched _),?_⟩
  intro id _ unknown test held
  have large : 2 < id := by
    by_cases low : id ≤ 2
    · exact False.elim (unknown (known id low))
    · omega
  rw [free _ _ large] at held
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test held

theorem equality_transfer (s : State roles)
    (transfer : ∀ m, Models final m → Models s m) : EqualityClosed s := by
  intro a b _ _ given
  have same : Equal final a b := fun m valid => given m (transfer m valid)
  cases equality_names a b same
  intro m _
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem headless_initial : HeadlessUnknown initial :=
  headless_transfer initial (fun m => (GeneralDepthTwoEvidence300.final_models m).mp) all_known

theorem headless_after : HeadlessUnknown after :=
  headless_transfer after (fun m => (GeneralDepthTwoSecondInstall300.models m).mp) all_known

theorem equality_initial : EqualityClosed initial :=
  equality_transfer initial (fun m => (GeneralDepthTwoEvidence300.final_models m).mp)

theorem equality_after : EqualityClosed after :=
  equality_transfer after (fun m => (GeneralDepthTwoSecondInstall300.models m).mp)

theorem closed_initial : GeneralNominalReobservationSteps.PointClosed initial.core.erased.current.context.state :=
  GeneralDepthTwoFinalScope300.point_closed

theorem closed_after : GeneralNominalReobservationSteps.PointClosed after.core.erased.current.context.state :=
  GeneralDepthTwoFinalScope300.point_closed

theorem same_effect (a b : Effect roles) (reg : a.registry = b.registry)
    (ctx : a.snapshot = b.snapshot) (plan : a.plan = b.plan) : a = b := by
  cases a
  cases b
  cases reg
  cases ctx
  cases plan
  rfl

end Yulang.GeneralDepthTwoEarlyShared300
