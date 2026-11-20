import Yulang.GeneralRebaseDepthProjectedPath286

/-! Reachable-state simulation and reflection for the actual compiled
one-output driver. Projection equality deliberately hides raw refreshes. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthSimulation286
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralRebaseOutputDepthSuccessor271 (support)
open GeneralRebaseOutputDepthTrace271 (observe)
open GeneralRebaseStep258 (done)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Hop InstallHop Post)
open GeneralRebaseDepthProjectedPath286 (silent observed_phase installed_observe)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseSourceStepDriver270 (next propose next_exact)

abbrev Driver := GeneralRebaseStep258.Step (propose support)

theorem no_install_after {s t : State roles} (post : Post s) (hit : InstallHop s t) : False := by
  have h := GeneralRebaseDepthPhase286.post_step post (GeneralRebaseDepthPhase286.as_step hit)
  have eq : t.plans.length = s.plans.length := by
    cases h
    rfl
  cases hit
  change s.plans.length + 1 = s.plans.length at eq
  omega

theorem shadow {s t : State roles} {n : Nat} (path : ActualPath initial s n)
    (step : Step registry root s t) :
    (Hop s t ∧ observe t = observe s) ∨ (InstallHop s t ∧ Driver (observe s) (observe t)) := by
  rcases GeneralRebaseDepthFullTrace286.decomposes path with early|crossed
  · have linked := GeneralRebaseDepthFullTrace286.linked_after early
    rcases GeneralRebaseDepthPhase286.pre_partition (GeneralRebaseDepthEnableShape286.as_pre linked) step with h|hit
    · exact Or.inl ⟨h,silent h⟩
    · right
      refine ⟨hit,(next_exact ..).mp ?_⟩
      rw [(observed_phase path).2.mpr (GeneralRebaseDepthEnableShape286.as_pre linked),
        installed_observe early hit]
      exact GeneralRebaseOutputDepthSuccessor271.one_step
  · have h := GeneralRebaseDepthPhase286.post_step (GeneralRebaseDepthFullTrace286.crosses_post crossed) step
    exact Or.inl ⟨h,silent h⟩

theorem exact_lift {s : State roles} {n : Nat} (path : ActualPath initial s n) (target) :
    Driver (observe s) target ↔ ∃ t, InstallHop s t ∧ observe t = target := by
  rcases GeneralRebaseDepthFullTrace286.decomposes path with early|crossed
  · have linked := GeneralRebaseDepthFullTrace286.linked_after early
    have before := (observed_phase path).2.mpr (GeneralRebaseDepthEnableShape286.as_pre linked)
    rw [before]
    unfold Driver
    rw [← next_exact]
    change GeneralRebaseOutputDepthSuccessor271.driveStep = some target ↔ _
    rw [GeneralRebaseOutputDepthSuccessor271.one_step]
    constructor
    · intro eq
      obtain ⟨t,hit⟩ := GeneralRebaseDepthPreAvailable286.offers linked
      exact ⟨t,hit,(installed_observe early hit).trans (Option.some.inj eq)⟩
    · rintro ⟨t,hit,view⟩
      exact congrArg some ((installed_observe early hit).symm.trans view)
  · have post := GeneralRebaseDepthFullTrace286.crosses_post crossed
    rw [(observed_phase path).1.mpr post]
    exact ⟨fun impossible => (GeneralRebaseSourceStepDriver270.terminal support _ impossible).elim,
      fun ⟨_,hit,_⟩ => (no_install_after post hit).elim⟩

theorem visible_iff_install {s t : State roles} {n : Nat} (path : ActualPath initial s n)
    (step : Step registry root s t) :
    observe t ≠ observe s ↔ InstallHop s t := by
  constructor
  · intro differ
    rcases shadow path step with ⟨_,same⟩|⟨hit,_⟩
    · exact (differ same).elim
    · exact hit
  · intro hit same
    rcases GeneralRebaseDepthFullTrace286.decomposes path with early|crossed
    · have before := (observed_phase path).2.mpr
        (GeneralRebaseDepthEnableShape286.as_pre (GeneralRebaseDepthFullTrace286.linked_after early))
      have impossible : ([] : List GeneralRebaseStep258.Fact) = support :=
        congrArg GeneralRebaseStep258.State.remaining ((installed_observe early hit).symm.trans (same.trans before))
      exact (by decide +kernel : ([] : List GeneralRebaseStep258.Fact) ≠ support) impossible
    · exact no_install_after (GeneralRebaseDepthFullTrace286.crosses_post crossed) hit

end Yulang.GeneralRebaseDepthSimulation286
