import Yulang.GeneralMixedCompoundPointFirstInstall308
import Yulang.GeneralMixedCompoundSourceFork308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralMixedCompoundPointFirstExact308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryOptionalInstall229 (model)
open GeneralMixedCompoundSourcePrefix308 (pointBefore firstRevision reobserve_models)
open GeneralMixedCompoundPointFirstPlan308 (effect frame pointFirst)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown no_refresh generated_only EqualityClosed)
open GeneralNominalVersionedJournal232 (Effect State)
open GeneralNominalReobservationSteps (revision_known pointClosed_no_revision)

theorem headless : HeadlessUnknown pointBefore := by
  obtain ⟨m,valid,none⟩ := GeneralMixedCompoundSourcePrefix308.headless
  refine ⟨m,(reobserve_models m).mpr valid,?_⟩
  intro id support missing test
  exact none id support (fun found => missing ((revision_known firstRevision id).mpr found)) test

theorem equality_closed : EqualityClosed pointBefore := by
  intro a b one two eq m raw
  exact GeneralMixedCompoundSourcePrefix308.equality_closed a b one two
    (fun m valid => eq m ((reobserve_models m).mpr valid)) m
    ((GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mp raw)

theorem same_effect (e : Effect roles) (enabled : Installable registry pointBefore e)
    (atRoot : e.plan.packet.site.occurrence = root) : e = effect := by
  have current := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,atRoot] at current
  have equal := GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl rfl rfl current frame
  rcases e with ⟨reg,snapshot,newPlan,proved,nominated,ready⟩
  dsimp only at equal
  have sameRegistry : reg = registry := enabled.registry_eq
  have sameSnapshot : snapshot = pointBefore.core := enabled.snapshot_eq
  subst reg; subst snapshot
  cases equal
  rfl

theorem exact_second {s : State roles} : Step registry root pointBefore s ↔ s = pointFirst := by
  constructor
  · rintro ⟨focus,generated,action⟩
    have rootOnly := generated_only rfl rfl generated
    cases action with
    | administrative a =>
      cases a with
      | enqueue linked absent => exact False.elim (absent _ (List.mem_singleton_self _) rootOnly.symm)
      | refresh ctx cert id present unknown newly =>
        exact False.elim (no_refresh headless cert present unknown newly)
      | equate a b one two eq novel =>
        exact False.elim (novel (equality_closed a b one two eq))
      | reobserve revision cert improves =>
        exact False.elim (pointClosed_no_revision
          (GeneralDictionaryJournalRefinement228Reobserve.point_closed [] [] []) revision improves)
    | refresh _ ctx cert id member unknown newly =>
      exact False.elim (no_refresh headless cert member unknown newly)
    | install e enabled novel =>
      exact congrArg (GeneralNominalVersionedInstall232.install pointBefore) (same_effect e enabled rootOnly)
    | merge a b one two _ novel =>
      cases List.mem_singleton.mp one
      cases List.mem_singleton.mp two
      exact False.elim (novel (.refl _))
  · rintro rfl
    exact GeneralMixedCompoundPointFirstInstall308.step

end Yulang.GeneralMixedCompoundPointFirstExact308
