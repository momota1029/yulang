import Yulang.GeneralMixedFullControlCode306

import Yulang.GeneralRebaseDepthSimulation286
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlStep306
open GeneralDictionaryOutputDepth252 (roles initial registry root)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Post Pre Hop InstallHop)
open GeneralMixedControlAtoms306 (BasicFacts)
open GeneralMixedControlMask306 (project)
open GeneralMixedControlBisim306 (Observe labelled is_equal_of_bits project_observe)
open GeneralMixedFullControlCode306
variable {s t : State roles} {n : Nat}

theorem support (path : ActualPath initial s n) : BasicFacts s := by
  have stock := GeneralRebaseDepthScalarOffer286.reached path
  refine ⟨stock.cache,stock.source,?_⟩
  intro q
  have leaf : q.val = 0 ∨ q.val = 1 := by omega
  rcases leaf with atZero|atOne
  · rw [atZero]
    obtain ⟨slot,atoms⟩ := stock.zero
    exact ⟨slot,atoms.name,atoms.upper,atoms.lower⟩
  · rw [atOne]
    obtain ⟨slot,atoms⟩ := stock.one
    exact ⟨slot,atoms.name,atoms.upper,atoms.lower⟩

theorem hop_action (either : Pre s ∨ Post s) (h : Hop s t) : ∃ q, Action (.scalar q) s t := by
  cases h with
  | refresh ctx cert id present past now =>
    have e : id = 0 ∨ id = 1 := either.elim
      (fun pre => GeneralRebaseDepthPreAnchor286.novel_position pre.anchor ctx cert id past now)
      (fun post => GeneralRebaseDepthPathAnchor285.fresh_position post.anchor ctx cert id past now)
    rcases e with rfl|rfl
    · exact ⟨0,.scalar (.refresh ctx cert present past now)⟩
    · exact ⟨1,.scalar (.refresh ctx cert present past now)⟩

theorem split (path : ActualPath initial s n) : Step registry root s t ↔ ∃ e, Action e s t := by
  constructor
  · intro step
    have phase := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path
    rcases phase with pre|post
    · rcases GeneralRebaseDepthPhase286.pre_partition pre step with hop|install
      · obtain ⟨q,taken⟩ := hop_action (Or.inl pre) hop
        exact ⟨.scalar q,taken⟩
      · exact ⟨.install,.install install⟩
    · obtain ⟨q,taken⟩ := hop_action (Or.inr post) (GeneralRebaseDepthPhase286.post_step post step)
      exact ⟨.scalar q,taken⟩
  · rintro ⟨_,h⟩
    exact action_step h

theorem install_keeps_bits {s t : State roles} (pre : Pre s) (h : InstallHop s t) : project t = project s := by
  apply is_equal_of_bits
  intro q
  rw [GeneralMixedControlMask306.bit,GeneralMixedControlMask306.bit,
    GeneralRebaseDepthSchedule286.known_same_on_install pre h q.val]

theorem install_comes_from_pre (path : ActualPath initial s n) (h : InstallHop s t) : Pre s := by
  have phase := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path
  exact phase.elim id (fun post =>
    (GeneralRebaseDepthSimulation286.no_install_after post h).elim)

theorem forward (path : ActualPath initial s n) {e : Event} (h : Action e s t) :
    fire e (code s) (code t) = true := by
  cases h with
  | install h =>
    have pre := install_comes_from_pre path h
    have clear : (!(code s).installed) = true := by rw [(marker path).2.mpr pre]; rfl
    have keep : (code s).scalars = (code t).scalars := (install_keeps_bits pre h).symm
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨clear,phase_installs h⟩,decide_eq_true keep⟩
  | scalar obs =>
    have yes := project_observe obs
    cases obs with
    | refresh _ _ _ _ _ =>
      simp [fire,refresh_phase,show (code _).scalars = project _ from rfl,yes]

theorem lifts (path : ActualPath initial s n) (e : Event) (goal : Code)
    (h : fire e (code s) goal = true) : ∃ t, Action e s t ∧ code t = goal := by
  cases e with
  | install =>
    simp only [fire,Bool.and_eq_true_iff,Bool.not_eq_true',decide_eq_true_eq] at h
    have pre := (marker path).2.mp h.1.1
    have linked : GeneralRebaseDepthEnableShape286.Linked s := by
      rcases GeneralRebaseDepthPreAvailable286.actual_reach path with before|after
      · exact before
      · exact (GeneralRebaseDepthPhase286.exclusive pre after).elim
    obtain ⟨dest,step⟩ := GeneralRebaseDepthPreAvailable286.offers linked
    refine ⟨dest,.install step,Code.ext ?_ ?_⟩
    · exact (phase_installs step).trans h.1.2.symm
    · exact (install_keeps_bits pre step).trans h.2
  | scalar q =>
    simp only [fire,Bool.and_eq_true_iff,decide_eq_true_eq] at h
    obtain ⟨dest,step,bits⟩ := (labelled (support path) goal.scalars q).mp h.2
    refine ⟨dest,.scalar step,Code.ext ?_ bits⟩
    have same : (code dest).installed = (code s).installed := by cases step; rfl
    exact same.trans h.1

theorem exact_labelled (path : ActualPath initial s n) (e : Event) (goal : Code) :
    fire e (code s) goal = true ↔ ∃ t, Action e s t ∧ code t = goal :=
  ⟨lifts path e goal,fun ⟨_,h,eq⟩ => eq ▸ forward path h⟩

end Yulang.GeneralMixedFullControlStep306
