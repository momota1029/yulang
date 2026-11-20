import Yulang.GeneralDeferredLadderRelayTerminal304

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeferredLadderRelayCount304
open GeneralDeferredLadderRelay304 (Relay advanceState step_exists step_unique)
open GeneralDeferredLadderRelayAdvance304 (advance)
open GeneralDeferredLadderRelayTerminal304 (halted exact_dictionary root_evidence)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralObservedLadderBudget301 (Counted)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralObservedLadderJournalCompiler301 (table)
open GeneralObservedLadderEvidence301 (dictionary)

def runAfter {n k cap s} (rel : Relay n k cap s) (length : Nat) (fit : k+length ≤ n+1) :
    Σ t : State roles, Relay n (k+length) fit t :=
  match length with
  | 0 => ⟨s,rel⟩
  | length+1 =>
    let prior := runAfter rel length (by omega)
    let hi : k+length ≤ n := by omega
    ⟨advanceState prior.2 hi,advance prior.2 hi⟩

theorem possible {n k cap s} (rel : Relay n k cap s) (length : Nat) (fit : k+length ≤ n+1) :
    Counted length s (runAfter rel length fit).1 := by
  induction length with
  | zero => exact .refl s
  | succ length ih =>
    exact .tail (ih (by omega)) (step_exists (runAfter rel length (by omega)).2 (by omega))

theorem halted_at_index {n i cap s} (eq : i = n+1) (rel : Relay n i cap s) (t : State roles) :
    ¬ RawStep s t := by
  subst i
  exact halted rel t

theorem indexed_terminal {n i cap s} (eq : i = n+1) (rel : Relay n i cap s) :
    (∀ fuel, GeneralGeneratedDictionaryRun299.run (table s) fuel 0 =
      if n+1 < fuel then some (dictionary (n+1)) else none) ∧
      ∀ m, Models s m → (boundary roles).Evidence registry s m displayRoot (dictionary (n+1)) := by
  subst i
  exact ⟨exact_dictionary rel,root_evidence rel⟩

theorem exact_run {n k cap s} (rel : Relay n k cap s) {length t}
    (path : Counted length s t) : ∃ fit : k+length ≤ n+1, t = (runAfter rel length fit).1 := by
  have go {l : Nat} {a b : State roles} (given : Counted l a b) (beginAt : a = s) :
      ∃ fit : k+l ≤ n+1, b = (runAfter rel l fit).1 := by
    induction given with
    | refl => exact ⟨cap,beginAt⟩
    | @tail l a mid b _ next ih =>
      obtain ⟨fit,rfl⟩ := ih beginAt
      let seen := runAfter rel l fit
      by_cases hi : k+l ≤ n
      · have exactTarget := (step_unique seen.2 hi _).mp next
        exact ⟨by omega,exactTarget⟩
      · exact False.elim (halted_at_index (by omega) seen.2 _ next)
  exact go path rfl

theorem counted_iff {n k cap s} (rel : Relay n k cap s) (length : Nat) (t : State roles) :
    Counted length s t ↔ ∃ fit : k+length ≤ n+1, t = (runAfter rel length fit).1 :=
  ⟨exact_run rel,by rintro ⟨fit,rfl⟩; exact possible rel length fit⟩

theorem halted_count {n k cap s} (rel : Relay n k cap s) {length t}
    (path : Counted length s t) (noMore : ∀ next, ¬ RawStep t next) : length = n+1-k := by
  obtain ⟨fit,rfl⟩ := exact_run rel path
  by_cases hi : k+length ≤ n
  · exact False.elim (noMore _ (step_exists (runAfter rel length fit).2 hi))
  · omega

theorem halted_outcome {n k cap s} (rel : Relay n k cap s) {length t}
    (path : Counted length s t) (noMore : ∀ next, ¬ RawStep t next) :
    length = n+1-k ∧
      (∀ fuel, GeneralGeneratedDictionaryRun299.run (table t) fuel 0 =
        if n+1 < fuel then some (dictionary (n+1)) else none) ∧
      ∀ m, Models t m → (boundary roles).Evidence registry t m displayRoot (dictionary (n+1)) := by
  have len := halted_count rel path noMore
  obtain ⟨fit,rfl⟩ := exact_run rel path
  exact ⟨len,indexed_terminal (by omega) (runAfter rel length fit).2⟩

theorem some_halted {n k cap s} (rel : Relay n k cap s) :
    ∃ t, Counted (n+1-k) s t ∧ ∀ next, ¬ RawStep t next := by
  let fit : k+(n+1-k) ≤ n+1 := by omega
  exact ⟨(runAfter rel _ fit).1,possible rel _ fit,
    halted_at_index (by omega) (runAfter rel _ fit).2⟩

end Yulang.GeneralDeferredLadderRelayCount304
