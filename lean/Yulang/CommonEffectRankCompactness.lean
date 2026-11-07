import Yulang.CommonEffectRankMonotonicity

/-! Uniform finite branch selection across all negative ranks. This does
not commute an operation-local universal with a witness or a parameter, and
does not assert constructor-depth monotonicity. -/
namespace Yulang.CommonEffectRankCompactness
open Common (Row)
open CommonEffectRankMonotonicity (Compare compare_rank_add_drop)

theorem finite_decreasing_choice (candidates : List α) (property : Nat → α → Prop)
    (down : ∀ lower upper, lower ≤ upper → ∀ candidate, property upper candidate → property lower candidate)
    (every : ∀ rank, ∃ candidate ∈ candidates, property rank candidate) :
    ∃ candidate ∈ candidates, ∀ rank, property rank candidate := by
  classical
  induction candidates with
  | nil => obtain ⟨_, member, _⟩ := every 0; cases member
  | cons first rest ih =>
    by_cases allFirst : ∀ rank, property rank first
    · exact ⟨first, List.mem_cons_self, allFirst⟩
    · obtain ⟨failedRank, fails⟩ := Classical.not_forall.mp allFirst
      have tailEvery (rank : Nat) : ∃ candidate ∈ rest, property rank candidate := by
        obtain ⟨candidate, member, accepted⟩ := every (max rank failedRank)
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (fails (down failedRank _ (Nat.le_max_right _ _) _ accepted))
        · exact ⟨candidate, member, down rank _ (Nat.le_max_left _ _) candidate accepted⟩
      obtain ⟨candidate, member, accepted⟩ := ih tailEvery
      exact ⟨candidate, List.mem_cons_of_mem _ member, accepted⟩

/-- The finite branch may be chosen once for ALL ranks. Candidate types and
their arbitrary rows are fixed throughout this theorem. -/
theorem finite_rank_exact (candidates : List (CommonFinite.Ty Row × CommonFinite.Ty Row)) :
    (∀ rank, ∃ candidate ∈ candidates, Compare rank candidate.1 candidate.2) ↔
      ∃ candidate ∈ candidates, CommonFinite.ProducerLe Common.rowLe candidate.1 candidate.2 := by
  constructor
  · intro every
    have down (lower upper : Nat) (le : lower ≤ upper) (candidate : CommonFinite.Ty Row × CommonFinite.Ty Row)
        (accepted : Compare upper candidate.1 candidate.2) : Compare lower candidate.1 candidate.2 := by
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
      exact compare_rank_add_drop lower extra candidate.1 candidate.2 accepted
    obtain ⟨candidate, member, accepted⟩ := finite_decreasing_choice candidates _ down every
    exact ⟨candidate, member, (CommonFinite.producerLe_iff_probe _ _).mpr accepted⟩
  · rintro ⟨candidate, member, accepted⟩ rank
    exact ⟨candidate, member, (CommonFinite.producerLe_iff_probe _ _).mp accepted rank⟩

end Yulang.CommonEffectRankCompactness
