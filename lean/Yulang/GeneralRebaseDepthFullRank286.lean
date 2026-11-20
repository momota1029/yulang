import Yulang.GeneralRebaseDepthPhase286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralRebaseDepthFullRank286
open GeneralDictionaryOutputDepth252 (roles root registry)
open GeneralRebaseDepthPreAnchor286 (initial)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralRebaseDepthPhase286 (Pre Post Hop InstallHop Covered exclusive)
open GeneralRebaseDepthPathRank285 (ActualPath pending)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralNominalState (Known)

noncomputable def weight (s : State roles) : Nat := by
  classical exact if Pre s then 1 else 0

noncomputable def rank (s : State roles) : Nat := weight s + GeneralRebaseDepthPathRank285.rank s

theorem weight_pre {s : State roles} (a : Pre s) : weight s = 1 := by
  classical simp only [weight,a,ite_true]

theorem weight_post {s : State roles} (a : Post s) : weight s = 0 := by
  classical
  have notPre : ¬ Pre s := fun other => exclusive other a
  simp only [weight,notPre,ite_false]

theorem rank_le_three (s : State roles) : rank s ≤ 3 := by
  have small := GeneralRebaseDepthPathRank285.le_two s
  have one : weight s ≤ 1 := by
    unfold weight
    split <;> omega
  unfold rank
  omega

theorem pre_drop {s t : State roles} (a : Pre s) (hop : Hop s t) :
    GeneralRebaseDepthPathRank285.rank t < GeneralRebaseDepthPathRank285.rank s := by
  classical
  cases hop with
  | refresh ctx cert n _ unknown known =>
    let target := refresh s ctx
    have strict : pending target n < pending s n := by
      unfold pending
      change (if Known ctx.state n then 0 else 1) < (if Known (snapshot s) n then 0 else 1)
      simp only [unknown,known,ite_true,ite_false,Nat.zero_lt_one]
    have zero := GeneralRebaseDepthPathRank285.monotone_known (t := target) cert.refines.known 0
    have one := GeneralRebaseDepthPathRank285.monotone_known (t := target) cert.refines.known 1
    have selected := GeneralRebaseDepthPreAnchor286.novel_position a.anchor ctx cert n unknown known
    change GeneralRebaseDepthPathRank285.rank target < GeneralRebaseDepthPathRank285.rank s
    unfold GeneralRebaseDepthPathRank285.rank
    rcases selected with rfl|rfl <;> omega

theorem scalar_same_at_install {s t : State roles} (a : Pre s) (hop : InstallHop s t) :
    GeneralRebaseDepthPathRank285.rank t = GeneralRebaseDepthPathRank285.rank s := by
  classical
  cases hop with
  | take e allowed atRoot _ =>
    have v := GeneralRebaseDepthPreInstall286.installed_uses_certified a.anchor a.plan allowed atRoot
    unfold GeneralRebaseDepthPathRank285.rank pending
    rw [propext (GeneralRebaseDepthCrossAnchor286.known_iff v 0),
      propext (GeneralRebaseDepthCrossAnchor286.known_iff v 1)]

theorem drops {s t : State roles} (a : Covered s) (step : Step registry root s t) : rank t < rank s := by
  rcases a with pre | post
  · rcases GeneralRebaseDepthPhase286.pre_partition pre step with hop|take
    · have target := GeneralRebaseDepthPhase286.pre_refresh pre hop
      unfold rank
      rw [weight_pre pre,weight_pre target]
      have less := pre_drop pre hop
      omega
    · have after := GeneralRebaseDepthPhase286.cross pre take
      unfold rank
      rw [weight_pre pre,weight_post after,scalar_same_at_install pre take]
      omega
  · have next := GeneralRebaseDepthPhase286.post_step post step
    have after := GeneralRebaseDepthPhase286.post_refresh post next
    unfold rank
    rw [weight_post post,weight_post after]
    simpa only [Nat.zero_add] using GeneralRebaseDepthPathRank285.drop post.anchor next

theorem all_paths {s t : State roles} {n : Nat} (a : Covered s) (seen : ActualPath s t n) :
    Covered t ∧ n + rank t ≤ rank s := by
  induction seen with
  | empty => exact ⟨a,by simp⟩
  | more _ step ih =>
    have less := drops ih.1 step
    exact ⟨GeneralRebaseDepthPhase286.covered_next ih.1 step,by omega⟩

theorem accessibility {s : State roles} (a : Covered s) :
    Acc (fun t s => Step registry root s t) s := by
  have finite := (measure rank).wf.apply s
  induction finite with
  | intro state _ ih =>
    constructor
    intro next step
    exact ih next (drops a step) (GeneralRebaseDepthPhase286.covered_next a step)

theorem complete_bound {t : State roles} {n : Nat} (seen : ActualPath initial t n) : n ≤ 3 := by
  have facts := (all_paths (.inl GeneralRebaseDepthPhase286.start) seen).2
  have bound := rank_le_three initial
  omega

theorem initial_accessible : Acc (fun t s => Step registry root s t) initial :=
  accessibility (.inl GeneralRebaseDepthPhase286.start)

end Yulang.GeneralRebaseDepthFullRank286
