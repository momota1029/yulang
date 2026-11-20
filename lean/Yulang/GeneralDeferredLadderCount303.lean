import Yulang.GeneralDeferredLadderOutcomes302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderCount303
open GeneralDeferredLadderAfterVariants302 (OwnedPhase step advanceFrom path_count variantOwned)
open GeneralDeferredLadderVariantExact302 (only_step halted)
open GeneralDeferredLadderOutcomes302 (terminal terminal_state root_evidence journal)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralObservedLadderBudget301 (Counted)
open GeneralObservedLadderJournalCompiler301 (table)
open GeneralObservedLadderEvidence301 (dictionary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

theorem count_from {n k : Nat} (p : OwnedPhase n k) (cap : k ≤ n+1)
    {count : Nat} {s : State roles} (path : Counted count p.state s) :
    ∃ fit : k+count ≤ n+1, s = (advanceFrom p count fit).state := by
  have go {l : Nat} {a b : State roles} (history : Counted l a b) (beginAt : a = p.state) :
      ∃ fit : k+l ≤ n+1, b = (advanceFrom p l fit).state := by
    induction history with
    | refl => exact ⟨cap,beginAt⟩
    | tail _ next ih =>
      obtain ⟨fit,rfl⟩ := ih beginAt
      obtain ⟨hi,rfl⟩ := only_step (advanceFrom p _ fit) fit _ next
      exact ⟨by omega,rfl⟩
  exact go path rfl

theorem count_exact {n k : Nat} (p : OwnedPhase n k) (cap : k ≤ n+1)
    (count : Nat) (s : State roles) :
    Counted count p.state s ↔ ∃ fit : k+count ≤ n+1, s = (advanceFrom p count fit).state :=
  ⟨count_from p cap,by rintro ⟨fit,rfl⟩; exact path_count p count fit⟩

theorem remaining_exact {n k : Nat} (p : OwnedPhase n k) (cap : k ≤ n+1)
    {count : Nat} {s : State roles} (path : Counted count p.state s)
    (noMore : ∀ next, ¬ RawStep s next) :
    count = n+1-k ∧ s = (terminal p cap).state := by
  obtain ⟨fit,rfl⟩ := count_from p cap path
  have out : count = n+1-k := by
    by_cases yep : count = n+1-k
    · exact yep
    · exfalso
      have ok : k+count ≤ n := by omega
      exact noMore _ (GeneralObservedLadderEnabled301.actual (advanceFrom p count fit).toPhase ok)
  constructor
  · exact out
  · rw [terminal_state]
    subst count
    rfl

theorem halted_count_iff {n k : Nat} (p : OwnedPhase n k) (cap : k ≤ n+1)
    (count : Nat) (s : State roles) :
    (Counted count p.state s ∧ ∀ next, ¬ RawStep s next) ↔
      count = n+1-k ∧ s = (terminal p cap).state := by
  constructor
  · rintro ⟨path,noMore⟩
    exact remaining_exact p cap path noMore
  · rintro ⟨rfl,rfl⟩
    exact ⟨GeneralDeferredLadderOutcomes302.suffix p cap,halted (terminal p cap)⟩

theorem suffix_readback {n k : Nat} (p : OwnedPhase n k) (cap : k ≤ n+1)
    {count : Nat} {s : State roles} (path : Counted count p.state s)
    (noMore : ∀ next, ¬ RawStep s next) :
    count = n+1-k ∧
    (∀ fuel, GeneralGeneratedDictionaryRun299.run (table s) fuel 0 =
      if n+1 < fuel then some (dictionary (n+1)) else none) ∧
    ∀ m : Assignment, Models s m → (boundary roles).Evidence registry s m displayRoot (dictionary (n+1)) := by
  obtain ⟨len,rfl⟩ := remaining_exact p cap path noMore
  exact ⟨len,journal (terminal p cap),root_evidence (terminal p cap)⟩

end Yulang.GeneralDeferredLadderCount303
