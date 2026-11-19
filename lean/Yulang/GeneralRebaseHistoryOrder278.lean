import Yulang.GeneralRebaseMicroProbe278

namespace Yulang.GeneralRebaseHistoryOrder278
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseInstallTimeline278 (installedCount observedCount)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Known)

theorem model_order_of_counts {M : Tick → Assignment → Prop} {R : Nat → Assignment → Prop}
    (atCount : ∀ t m, M t m ↔ R (installedCount t) m)
    (restriction : ∀ a b, a ≤ b → ∀ m, R b m → R a m)
    (bad : Nat → Assignment) (patch : ∀ t i, M t (bad i) ↔ installedCount t ≤ i)
    (a b : Tick) : (∀ m, M b m → M a m) ↔ installedCount a ≤ installedCount b := by
  constructor
  · intro subset
    let i := installedCount b
    have inB : M b (bad i) := (patch b i).mpr (Nat.le_refl _)
    exact (patch a i).mp (subset _ inB)
  · intro bound m h
    exact (atCount a m).mpr (restriction _ _ bound m ((atCount b m).mp h))

theorem version_atCount (t : Tick) (m : Assignment) :
    Models (GeneralRebaseVersionMicro278.raw t) m ↔
      Models (GeneralDictionaryVersionLoopIteration239.state (installedCount t)) m := by
  rcases t with ⟨n,p⟩
  cases p
  · rfl
  · exact (GeneralRebaseVersionPrivate278.refreshed_exact n m).symm.trans
      (GeneralRebaseVersionPrivate278.reobserved_exact n m).symm
  · exact (GeneralRebaseVersionPrivate278.reobserved_exact n m).symm

theorem loose_atCount (t : Tick) (m : Assignment) :
    Models (GeneralRebaseLooseMicro278.raw t) m ↔
      Models (GeneralDictionaryLooseIterationIteration240.state (installedCount t)) m := by
  rcases t with ⟨n,p⟩
  cases p
  · rfl
  · exact (GeneralRebaseLoosePrivate278.refreshed_exact n m).symm.trans
      (GeneralRebaseLoosePrivate278.reobserved_exact n m).symm
  · exact (GeneralRebaseLoosePrivate278.reobserved_exact n m).symm

theorem version_order (a b : Tick) :
    (∀ m, Models (GeneralRebaseVersionMicro278.raw b) m →
          Models (GeneralRebaseVersionMicro278.raw a) m) ↔
      installedCount a ≤ installedCount b :=
  model_order_of_counts version_atCount GeneralRebaseInstallTimeline278.Version.round_restriction
    GeneralDictionaryVersionLoopFamilyNovel239.bad GeneralRebaseInstallTimeline278.Version.patch_exact a b

theorem loose_order (a b : Tick) :
    (∀ m, Models (GeneralRebaseLooseMicro278.raw b) m →
          Models (GeneralRebaseLooseMicro278.raw a) m) ↔
      installedCount a ≤ installedCount b :=
  model_order_of_counts loose_atCount GeneralRebaseInstallTimeline278.Loose.round_restriction
    GeneralDictionaryLooseFamilyNovel240.bad GeneralRebaseInstallTimeline278.Loose.patch_exact a b

theorem equality_from_order {M : Tick → Assignment → Prop}
    (order : ∀ a b, (∀ m, M b m → M a m) ↔ installedCount a ≤ installedCount b)
    (a b : Tick) : (∀ m, M a m ↔ M b m) ↔ installedCount a = installedCount b := by
  constructor
  · intro equal
    exact Nat.le_antisymm ((order a b).mp (fun m => (equal m).mpr)) ((order b a).mp (fun m => (equal m).mp))
  · intro eq m
    exact ⟨(order b a).mpr (Nat.le_of_eq eq.symm) m,(order a b).mpr (Nat.le_of_eq eq) m⟩

theorem version_equality (a b : Tick) :
    (∀ m, Models (GeneralRebaseVersionMicro278.raw a) m ↔
          Models (GeneralRebaseVersionMicro278.raw b) m) ↔
      installedCount a = installedCount b := equality_from_order version_order a b

theorem loose_equality (a b : Tick) :
    (∀ m, Models (GeneralRebaseLooseMicro278.raw a) m ↔
          Models (GeneralRebaseLooseMicro278.raw b) m) ↔
      installedCount a = installedCount b := equality_from_order loose_order a b

theorem lower_order {K : Tick → Nat → Prop} (exactKnown : ∀ t i, K t i ↔ i < observedCount t)
    (a b : Tick) : (∀ i, K a i → K b i) ↔ observedCount a ≤ observedCount b := by
  constructor
  · intro subset
    by_cases h : observedCount a ≤ observedCount b
    · exact h
    · exfalso
      have fromA := (exactKnown a (observedCount b)).mpr (by omega)
      have bound := (exactKnown b (observedCount b)).mp (subset _ fromA)
      omega
  · intro h i held
    exact (exactKnown b i).mpr (Nat.lt_of_lt_of_le ((exactKnown a i).mp held) h)

theorem version_lower_order (a b : Tick) :
    (∀ i, Known (GeneralRebaseVersionMicro278.raw a).core.erased.current.context.state
             (GeneralDictionaryVersionLoopNames238.lower (i+1)) →
          Known (GeneralRebaseVersionMicro278.raw b).core.erased.current.context.state
             (GeneralDictionaryVersionLoopNames238.lower (i+1))) ↔
      observedCount a ≤ observedCount b := lower_order GeneralRebaseVersionKnown278.prefix_known a b

theorem loose_lower_order (a b : Tick) :
    (∀ i, Known (GeneralRebaseLooseMicro278.raw a).core.erased.current.context.state
             (GeneralDictionaryLooseFamilyNames240.lower (i+1)) →
          Known (GeneralRebaseLooseMicro278.raw b).core.erased.current.context.state
             (GeneralDictionaryLooseFamilyNames240.lower (i+1))) ↔
      observedCount a ≤ observedCount b := lower_order GeneralRebaseLooseKnown278.prefix_known a b

/-- Complete only for the two displayed predicates: full model inclusion and the
    set of recognized lower names. Not a raw transition or registry key. -/
def observationKey (t : Tick) : Nat × Nat := (installedCount t,observedCount t)

theorem observationKey_collision (a b : Tick) :
    observationKey a = observationKey b ↔
      a = b ∨
      ∃ n, (a = ⟨n,.refreshed⟩ ∧ b = ⟨n+1,.enter⟩) ∨
           (b = ⟨n,.refreshed⟩ ∧ a = ⟨n+1,.enter⟩) := by
  constructor
  · rcases a with ⟨a,pa⟩
    rcases b with ⟨b,pb⟩
    intro same
    have hi := congrArg Prod.fst same
    have ho := congrArg Prod.snd same
    cases pa <;> cases pb <;> simp only [observationKey,installedCount,observedCount] at hi ho
    · exact Or.inl (by rw [hi])
    · omega
    · exact Or.inr ⟨b,Or.inr ⟨rfl,by rw [hi]⟩⟩
    · omega
    · have equal : a = b := ho
      exact Or.inl (by rw [equal])
    · omega
    · exact Or.inr ⟨a,Or.inl ⟨rfl,by rw [← hi]⟩⟩
    · omega
    · have equal : a = b := by omega
      exact Or.inl (by rw [equal])
  · rintro (rfl|⟨n,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩) <;> rfl

def observedRefines (a b : Tick) : Bool :=
  decide (installedCount a ≤ installedCount b ∧ observedCount a ≤ observedCount b)

theorem version_refines (a b : Tick) : observedRefines a b = true ↔
    (∀ m, Models (GeneralRebaseVersionMicro278.raw b) m →
          Models (GeneralRebaseVersionMicro278.raw a) m) ∧
    (∀ i, Known (GeneralRebaseVersionMicro278.raw a).core.erased.current.context.state
             (GeneralDictionaryVersionLoopNames238.lower (i+1)) →
          Known (GeneralRebaseVersionMicro278.raw b).core.erased.current.context.state
             (GeneralDictionaryVersionLoopNames238.lower (i+1))) :=
  (decide_eq_true_iff).trans (and_congr (version_order a b).symm (version_lower_order a b).symm)

theorem loose_refines (a b : Tick) : observedRefines a b = true ↔
    (∀ m, Models (GeneralRebaseLooseMicro278.raw b) m →
          Models (GeneralRebaseLooseMicro278.raw a) m) ∧
    (∀ i, Known (GeneralRebaseLooseMicro278.raw a).core.erased.current.context.state
             (GeneralDictionaryLooseFamilyNames240.lower (i+1)) →
          Known (GeneralRebaseLooseMicro278.raw b).core.erased.current.context.state
             (GeneralDictionaryLooseFamilyNames240.lower (i+1))) :=
  (decide_eq_true_iff).trans (and_congr (loose_order a b).symm (loose_lower_order a b).symm)

end Yulang.GeneralRebaseHistoryOrder278
