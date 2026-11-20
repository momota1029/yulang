import Yulang.GeneralRebaseWitnessExistence297
import Yulang.GeneralRebaseInstallTimeline278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseSignedHistory297
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseSignedModels297 (Conditions Test)

/-- If one raw model can be lost at most once, a finite prefix needing n
negative witnesses cannot be covered by fewer than n assignments. -/
theorem at_least {A : Type} (rejects : Nat → A → Prop)
    (disjoint : ∀ i j, i < j → ∀ a, rejects i a → ¬ rejects j a)
    (xs : List A) (n : Nat)
    (covers : ∀ i < n, ∃ a ∈ xs, rejects i a) : n ≤ xs.length := by
  classical
  let f : Fin n → A := fun i => Classical.choose (covers i i.isLt)
  have sound (i : Fin n) : f i ∈ xs ∧ rejects i (f i) := Classical.choose_spec (covers i i.isLt)
  have injective : Function.Injective f := by
    intro a b eq
    apply Fin.ext
    apply Classical.byContradiction
    intro ne
    rcases Nat.lt_or_gt_of_ne ne with small|large
    · exact disjoint a b small (f a) (sound a).2 (eq.symm ▸ (sound b).2)
    · exact disjoint b a large (f b) (sound b).2 (eq ▸ (sound a).2)
  let ys := (List.finRange n).map f
  have nodup : ys.Nodup := by
    change ((List.finRange n).map f).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    exact (List.nodup_finRange n).imp (fun ne eq => ne (injective eq))
  have subset : ys ⊆ xs := by
    intro a present
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp present
    exact (sound i).1
  simpa [ys] using List.Nodup.length_le_of_subset nodup subset

theorem no_fixed_table {A : Type} (rejects : Nat → A → Prop)
    (disjoint : ∀ i j, i < j → ∀ a, rejects i a → ¬ rejects j a)
    (xs : List A) : ¬ ∀ i, ∃ a ∈ xs, rejects i a := by
  intro all
  have bad := at_least rejects disjoint xs (xs.length+1) (fun i _ => all i)
  omega

namespace Version
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralRebaseVersionMicro278 (installed)
open GeneralDictionaryVersionLoopFamilyNovel239 (bad)

def dropped (n : Nat) (m : Assignment) : Prop := Test (state n) (plan n) .reject m

theorem exact_loss (n : Nat) (m : Assignment) :
    dropped n m ↔ Models (state n) m ∧ ¬ Models (installed n) m := by
  rw [GeneralRebaseVersionPrivate278.installed_exact]
  have live := GeneralDictionaryVersionLoopInstall239.classes (stages n).shape m
  change (Models (state n) m ∧ ¬ (GeneralNominalVersionedPlans231.Holds (plan n) m ∧ _)) ↔ _
  exact ⟨fun ⟨old,no⟩ => ⟨old,fun got => no ⟨got.2,live⟩⟩,
    fun ⟨old,no⟩ => ⟨old,fun got => no ⟨old,got.1⟩⟩⟩

theorem bad_witness (n : Nat) : dropped n (bad n) :=
  (exact_loss n _).mpr ⟨(GeneralRebaseVersionPrivate278.raw_strict n).1,
    (GeneralRebaseVersionPrivate278.raw_strict n).2.1⟩

theorem disjoint (a b : Nat) (earlier : a < b) (m : Assignment)
    (lost : dropped a m) (later : dropped b m) : False := by
  have old := (exact_loss b m).mp later
  have since := GeneralRebaseInstallTimeline278.Version.round_restriction (a+1) b earlier m old.1
  have still := (GeneralRebaseVersionPrivate278.refreshed_exact a m).mp
    ((GeneralRebaseVersionPrivate278.reobserved_exact a m).mp since)
  exact ((exact_loss a m).mp lost).2 still

theorem no_universal_rejections (xs : List Assignment) :
    ¬ ∀ n, ∃ a ∈ xs, Test (state n) (plan n) .reject a :=
  no_fixed_table dropped disjoint xs

theorem finite_prefix_minimum (limit : Nat) :
    ∃ xs : List Assignment, xs.length = limit ∧
      (∀ n < limit, ∃ a ∈ xs, dropped n a) ∧
      ∀ ys : List Assignment, (∀ n < limit, ∃ a ∈ ys, dropped n a) → limit ≤ ys.length :=
  ⟨(List.range limit).map bad,by simp,fun n below =>
    ⟨bad n,List.mem_map_of_mem (List.mem_range.mpr below),bad_witness n⟩,
    fun ys covered => at_least dropped disjoint ys limit covered⟩

end Version

namespace Loose
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseIterationBook240 (plan)
open GeneralRebaseLooseMicro278 (installed)
open GeneralDictionaryLooseFamilyNovel240 (bad)

def dropped (n : Nat) (m : Assignment) : Prop := Test (state n) (plan n) .reject m

theorem exact_loss (n : Nat) (m : Assignment) :
    dropped n m ↔ Models (state n) m ∧ ¬ Models (installed n) m := by
  rw [GeneralRebaseLoosePrivate278.installed_exact]
  have live := GeneralDictionaryLooseIterationInstall240.classes (stages n).shape m
  change (Models (state n) m ∧ ¬ (GeneralNominalVersionedPlans231.Holds (plan n) m ∧ _)) ↔ _
  exact ⟨fun ⟨old,no⟩ => ⟨old,fun got => no ⟨got.2,live⟩⟩,
    fun ⟨old,no⟩ => ⟨old,fun got => no ⟨old,got.1⟩⟩⟩

theorem bad_witness (n : Nat) : dropped n (bad n) :=
  (exact_loss n _).mpr ⟨(GeneralRebaseLoosePrivate278.raw_strict n).1,
    (GeneralRebaseLoosePrivate278.raw_strict n).2.1⟩

theorem disjoint (a b : Nat) (earlier : a < b) (m : Assignment)
    (lost : dropped a m) (later : dropped b m) : False := by
  have old := (exact_loss b m).mp later
  have since := GeneralRebaseInstallTimeline278.Loose.round_restriction (a+1) b earlier m old.1
  have still := (GeneralRebaseLoosePrivate278.refreshed_exact a m).mp
    ((GeneralRebaseLoosePrivate278.reobserved_exact a m).mp since)
  exact ((exact_loss a m).mp lost).2 still

theorem no_universal_rejections (xs : List Assignment) :
    ¬ ∀ n, ∃ a ∈ xs, Test (state n) (plan n) .reject a :=
  no_fixed_table dropped disjoint xs

theorem finite_prefix_minimum (limit : Nat) :
    ∃ xs : List Assignment, xs.length = limit ∧
      (∀ n < limit, ∃ a ∈ xs, dropped n a) ∧
      ∀ ys : List Assignment, (∀ n < limit, ∃ a ∈ ys, dropped n a) → limit ≤ ys.length :=
  ⟨(List.range limit).map bad,by simp,fun n below =>
    ⟨bad n,List.mem_map_of_mem (List.mem_range.mpr below),bad_witness n⟩,
    fun ys covered => at_least dropped disjoint ys limit covered⟩

end Loose

end Yulang.GeneralRebaseSignedHistory297
