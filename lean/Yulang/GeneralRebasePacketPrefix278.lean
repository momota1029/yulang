import Yulang.GeneralRebaseHistoryOrder278

namespace Yulang.GeneralRebasePacketPrefix278
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseInstallTimeline278 (installedCount)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (Holds)

theorem prefix_induction {M P : Nat → Prop} (step : ∀ n, M (n+1) ↔ M n ∧ P n)
    (n : Nat) : M n ↔ M 0 ∧ ∀ i, i < n → P i := by
  induction n with
  | zero => exact ⟨fun h => ⟨h,fun i lt => False.elim (Nat.not_lt_zero i lt)⟩,And.left⟩
  | succ n ih =>
    rw [step n,ih]
    constructor
    · rintro ⟨⟨base,past⟩,latest⟩
      refine ⟨base,?_⟩
      intro i h
      have le : i ≤ n := Nat.le_of_lt_succ h
      cases Nat.eq_or_lt_of_le le with
      | inl same => exact same ▸ latest
      | inr older => exact past i older
    · rintro ⟨base,past⟩
      exact ⟨⟨base,fun i h => past i (Nat.lt_succ_of_lt h)⟩,past n (Nat.lt_succ_self n)⟩

theorem version_round_step (n : Nat) (m : Assignment) :
    Models (GeneralDictionaryVersionLoopIteration239.state (n+1)) m ↔
      Models (GeneralDictionaryVersionLoopIteration239.state n) m ∧
      Holds (GeneralDictionaryVersionLoopBook239.plan n) m :=
  (GeneralRebaseVersionPrivate278.reobserved_exact n m).trans
    ((GeneralRebaseVersionPrivate278.refreshed_exact n m).trans
      (GeneralRebaseVersionPrivate278.installed_exact n m))

theorem loose_round_step (n : Nat) (m : Assignment) :
    Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) m ↔
      Models (GeneralDictionaryLooseIterationIteration240.state n) m ∧
      Holds (GeneralDictionaryLooseIterationBook240.plan n) m :=
  (GeneralRebaseLoosePrivate278.reobserved_exact n m).trans
    ((GeneralRebaseLoosePrivate278.refreshed_exact n m).trans
      (GeneralRebaseLoosePrivate278.installed_exact n m))

theorem version_prefix (t : Tick) (m : Assignment) :
    Models (GeneralRebaseVersionMicro278.raw t) m ↔
      Models (GeneralDictionaryVersionLoopIteration239.state 0) m ∧
      ∀ i, i < installedCount t → Holds (GeneralDictionaryVersionLoopBook239.plan i) m :=
  (GeneralRebaseHistoryOrder278.version_atCount t m).trans
    (prefix_induction
      (M := fun n => Models (GeneralDictionaryVersionLoopIteration239.state n) m)
      (P := fun n => Holds (GeneralDictionaryVersionLoopBook239.plan n) m)
      (fun n => version_round_step n m) (installedCount t))

theorem loose_prefix (t : Tick) (m : Assignment) :
    Models (GeneralRebaseLooseMicro278.raw t) m ↔
      Models (GeneralDictionaryLooseIterationIteration240.state 0) m ∧
      ∀ i, i < installedCount t → Holds (GeneralDictionaryLooseIterationBook240.plan i) m :=
  (GeneralRebaseHistoryOrder278.loose_atCount t m).trans
    (prefix_induction
      (M := fun n => Models (GeneralDictionaryLooseIterationIteration240.state n) m)
      (P := fun n => Holds (GeneralDictionaryLooseIterationBook240.plan n) m)
      (fun n => loose_round_step n m) (installedCount t))

theorem version_no_eventual_equality (baseRound : Nat) :
    ¬ (∀ n, baseRound ≤ n → ∀ m,
      Models (GeneralDictionaryVersionLoopIteration239.state baseRound) m ↔
      Models (GeneralDictionaryVersionLoopIteration239.state n) m) := by
  intro stable
  have impossible := (GeneralRebaseHistoryOrder278.version_equality
    ⟨baseRound,.enter⟩ ⟨baseRound+1,.enter⟩).mp (stable (baseRound+1) (Nat.le_succ _))
  change baseRound = baseRound+1 at impossible
  omega

theorem loose_no_eventual_equality (baseRound : Nat) :
    ¬ (∀ n, baseRound ≤ n → ∀ m,
      Models (GeneralDictionaryLooseIterationIteration240.state baseRound) m ↔
      Models (GeneralDictionaryLooseIterationIteration240.state n) m) := by
  intro stable
  have impossible := (GeneralRebaseHistoryOrder278.loose_equality
    ⟨baseRound,.enter⟩ ⟨baseRound+1,.enter⟩).mp (stable (baseRound+1) (Nat.le_succ _))
  change baseRound = baseRound+1 at impossible
  omega

end Yulang.GeneralRebasePacketPrefix278
