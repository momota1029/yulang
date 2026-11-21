import Yulang.GeneralMixedControlLiveness306

namespace Yulang.GeneralMixedControlRank306
open GeneralMixedControlMask306
open GeneralMixedControlLiveness306
open GeneralDictionaryOutputDepth252 (root registry roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)

theorem rank_successors (x : Mask) (k : Nat) :
    (∃ y, moves x y = true ∧ rank y = k) ↔ k < rank x := by
  constructor
  · rintro ⟨y,step,rfl⟩
    exact rank_moves x y step
  · intro small
    have listed := exhaustive x
    simp only [masks,List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl|rfl|rfl|rfl
    · change k < 2 at small
      have values : k = 0 ∨ k = 1 := by omega
      rcases values with rfl|rfl
      · exact ⟨full,rfl,rfl⟩
      · exact ⟨onlyZero,rfl,rfl⟩
    · change k < 1 at small
      have z : k = 0 := by omega
      subst k
      exact ⟨full,rfl,rfl⟩
    · change k < 1 at small
      have z : k = 0 := by omega
      subst k
      exact ⟨full,rfl,rfl⟩
    · change k < 0 at small
      omega

theorem raw_rank_exact {s : State roles} {len : Nat} (path : ActualPath installed s len) (k : Nat) :
    (∃ t, Step registry root s t ∧ rank (project t) = k) ↔ k < rank (project s) := by
  rw [← rank_successors]
  constructor
  · rintro ⟨t,step,h⟩
    exact ⟨project t,(GeneralMixedControlBisim306.unlabelled path _).mpr ⟨t,step,rfl⟩,h⟩
  · rintro ⟨target,edge,h⟩
    obtain ⟨t,step,rfl⟩ := (GeneralMixedControlBisim306.unlabelled path target).mp edge
    exact ⟨t,step,h⟩

/-- The rank is the exact fully unlabelled transition quotient. It discards
the identity of the newly known scalar, unlike the four-state mask. -/
theorem rank_matches {s t : State roles} {ns nt : Nat} (p : ActualPath installed s ns)
    (q : ActualPath installed t nt) (same : rank (project s) = rank (project t))
    (before : Step registry root s next) :
    ∃ later, Step registry root t later ∧ rank (project next) = rank (project later) := by
  have smaller := (raw_rank_exact p _).mp ⟨next,before,rfl⟩
  rw [same] at smaller
  obtain ⟨later,taken,equal⟩ := (raw_rank_exact q _).mpr smaller
  exact ⟨later,taken,equal.symm⟩

def StrongBisim (R : Mask → Mask → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ x', moves x x' = true → ∃ y', moves y y' = true ∧ R x' y') ∧
    (∀ y', moves y y' = true → ∃ x', moves x x' = true ∧ R x' y')

theorem rank_bisim : StrongBisim (fun x y => rank x = rank y) := by
  intro x y same
  constructor
  · intro next h
    obtain ⟨later,equal,rankEq⟩ := (rank_successors y (rank next)).mpr (same ▸ rank_moves x next h)
    exact ⟨later,equal,rankEq.symm⟩
  · intro later h
    obtain ⟨next,equal,rankEq⟩ := (rank_successors x (rank later)).mpr (same.symm ▸ rank_moves y later h)
    exact ⟨next,equal,rankEq⟩

theorem any_bisim_respects_rank {R : Mask → Mask → Prop} (hyp : StrongBisim R)
    (x y : Mask) (related : R x y) : rank x = rank y := by
  by_cases less : rank x < rank y
  · obtain ⟨y',yes,levels⟩ := (rank_successors y (rank x)).mpr less
    obtain ⟨x',seen,small⟩ := (hyp x y related).2 y' yes
    have deeper := any_bisim_respects_rank hyp x' y' small
    have drop := rank_moves x x' seen
    omega
  · by_cases more : rank y < rank x
    · obtain ⟨x',yes,levels⟩ := (rank_successors x (rank y)).mpr more
      obtain ⟨y',seen,small⟩ := (hyp x y related).1 x' yes
      have deeper := any_bisim_respects_rank hyp x' y' small
      have drop := rank_moves y y' seen
      omega
    · omega
termination_by rank x + rank y
decreasing_by
  all_goals
    have a := rank_moves x x' (by assumption)
    have b := rank_moves y y' (by assumption)
    omega

end Yulang.GeneralMixedControlRank306
