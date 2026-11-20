import Yulang.GeneralRebaseDepthScalarOffer286

/-! Exact terminal frontier and realizable ordering of the independent scalar
marks and nested installation, proved over actual mixed-kernel steps. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthSchedule286
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralRebaseDepthPathRank285 (ActualPath pending)
open GeneralRebaseDepthPhase286 (Post Pre Hop InstallHop)
open GeneralNominalState (Known)

def Both (s : State roles) : Prop := Known (snapshot s) 0 ∧ Known (snapshot s) 1

def Halted (s : State roles) : Prop := ∀ next, ¬ Step registry root s next

theorem scalar_rank_zero {s : State roles} (both : Both s) :
    GeneralRebaseDepthPathRank285.rank s = 0 := by
  classical
  unfold GeneralRebaseDepthPathRank285.rank pending
  simp only [both.1,both.2,ite_true,Nat.add_zero]

theorem halt_of_done {s : State roles} (after : Post s) (both : Both s) : Halted s := by
  intro t move
  have less := GeneralRebaseDepthPathRank285.drop after.anchor
    (GeneralRebaseDepthPhase286.post_step after move)
  rw [scalar_rank_zero both] at less
  omega

theorem exact_terminal {s : State roles} {steps : Nat} (path : ActualPath initial s steps) :
    Halted s ↔ Post s ∧ Both s := by
  constructor
  · intro halt
    exact ⟨GeneralRebaseDepthFullTrace286.crosses_post (GeneralRebaseDepthFullTrace286.maximal_crosses path halt),
      GeneralRebaseDepthScalarOffer286.halt_known path halt 0 (by decide),
      GeneralRebaseDepthScalarOffer286.halt_known path halt 1 (by decide)⟩
  · rintro ⟨after,both⟩
    exact halt_of_done after both

theorem hop_step {s t : State roles} (h : Hop s t) : Step registry root s t := by
  cases h with
  | refresh ctx cert n present old new =>
    exact ⟨root,.root,.refresh root ctx cert n present old new⟩

inductive Event where
 | install
 | zero
 | one
 deriving DecidableEq

def Open (s : State roles) : Event → Prop
 | .install => ¬ Post s
 | .zero => ¬ Known (snapshot s) 0
 | .one => ¬ Known (snapshot s) 1

def Done (s : State roles) : Event → Prop
 | .install => Post s
 | .zero => Known (snapshot s) 0
 | .one => Known (snapshot s) 1

structure Move (label : Event) (s t : State roles) : Prop where
  actual : Step registry root s t
  done : Done t label
  only : ∀ other, other ≠ label → (Open t other ↔ Open s other)

theorem scalar_move {s : State roles} {steps : Nat}
    (path : ActualPath initial s steps) {n : Nat} (small : n ≤ 1)
    (unclear : ¬ Known (snapshot s) n) :
    ∃ t, Hop s t ∧ Known (snapshot t) n ∧ (Post t ↔ Post s) ∧
      ∀ i, i ≠ n → (Known (snapshot t) i ↔ Known (snapshot s) i) := by
  obtain ⟨slot,seed,action⟩ := GeneralRebaseDepthScalarOffer286.offers
    (GeneralRebaseDepthScalarOffer286.reached path) small unclear
  let t := refresh s (GeneralRebaseDepthScalarMark286.target seed unclear)
  refine ⟨t,action,GeneralRebaseDepthScalarMark286.selected seed unclear,?_,
    fun _ differs => GeneralRebaseDepthScalarMark286.target_other seed unclear differs⟩
  rcases GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path with pre|post
  · have nextPre := GeneralRebaseDepthPhase286.pre_refresh pre action
    exact ⟨fun h => (GeneralRebaseDepthPhase286.exclusive nextPre h).elim,
      fun h => (GeneralRebaseDepthPhase286.exclusive pre h).elim⟩
  · have nextPost := GeneralRebaseDepthPhase286.post_refresh post action
    exact ⟨fun _ => post,fun _ => nextPost⟩

theorem known_same_on_install {s t : State roles} (pre : Pre s) (h : InstallHop s t) (n : Nat) :
    Known (snapshot t) n ↔ Known (snapshot s) n := by
  cases h with
  | take e allowed same _ =>
    exact GeneralRebaseDepthCrossAnchor286.known_iff
      (GeneralRebaseDepthPreInstall286.installed_uses_certified pre.anchor pre.plan allowed same) n

theorem realize {s : State roles} {steps : Nat}
    (path : ActualPath initial s steps) (e : Event) (openNow : Open s e) :
    ∃ t, Move e s t := by
  cases e with
  | install =>
    rcases GeneralRebaseDepthFullTrace286.decomposes path with quiet|crossed
    · have linked := GeneralRebaseDepthFullTrace286.linked_after quiet
      obtain ⟨t,install⟩ := GeneralRebaseDepthPreAvailable286.offers linked
      have pre := GeneralRebaseDepthEnableShape286.as_pre linked
      refine ⟨t,GeneralRebaseDepthPhase286.as_step install,
        GeneralRebaseDepthPhase286.cross pre install,?_⟩
      intro other different
      cases other with
      | install => exact (different rfl).elim
      | zero => exact not_congr (known_same_on_install pre install 0)
      | one => exact not_congr (known_same_on_install pre install 1)
    · exact (openNow (GeneralRebaseDepthFullTrace286.crosses_post crossed)).elim
  | zero =>
    obtain ⟨t,h,yes,phase,same⟩ := scalar_move path (n := 0) (by decide) openNow
    refine ⟨t,hop_step h,yes,?_⟩
    intro other different
    cases other with
    | install => exact not_congr phase
    | zero => exact (different rfl).elim
    | one => exact not_congr (same 1 (by decide))
  | one =>
    obtain ⟨t,h,yes,phase,same⟩ := scalar_move path (n := 1) (by decide) openNow
    refine ⟨t,hop_step h,yes,?_⟩
    intro other different
    cases other with
    | install => exact not_congr phase
    | zero => exact not_congr (same 0 (by decide))
    | one => exact (different rfl).elim

end Yulang.GeneralRebaseDepthSchedule286
