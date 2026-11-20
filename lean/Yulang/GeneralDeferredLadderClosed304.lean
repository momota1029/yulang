import Yulang.GeneralDeferredLadderRelayCount304
import Yulang.GeneralDeferredLadderAgreement303

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeferredLadderClosed304
open GeneralDeferredLadderRelay304 (Relay refPhase refState initial advanceState step_unique)
open GeneralDeferredLadderRelayAdvance304 (advance)
open GeneralDeferredLadderRelayCount304 (halted_at_index indexed_terminal)
open GeneralDeferredLadderExact302 (RawStep Promotion only_step)
open GeneralObservedLadderBudget301 (Counted)
open GeneralObservedLadderRefresh301 (before)
open GeneralObservedLadderJournalCompiler301 (table)
open GeneralObservedLadderEvidence301 (dictionary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)

def PhaseAt (n length : Nat) (s : State roles) : Prop :=
  (∃ cap : length ≤ n+1, s = refState n length cap) ∨
    ∃ k : Nat, ∃ cap : k ≤ n+1, Nonempty (Relay n k cap s) ∧ length = k+1

theorem classification (n : Nat) {length s} (path : Counted length (before n) s) :
    PhaseAt n length s := by
  have go {len : Nat} {a b : State roles} (given : Counted len a b) (start : a = before n) :
      PhaseAt n len b := by
    induction given with
    | refl => exact Or.inl ⟨by omega,start⟩
    | @tail len a middle b _ next ih =>
      rcases ih start with ⟨cap,rfl⟩ | ⟨k,cap,⟨rel⟩,atLength⟩
      · rcases only_step n len cap b next with ⟨hi,rfl⟩ | ⟨target,cert,known,rfl⟩
        · exact Or.inl ⟨by omega,rfl⟩
        · exact Or.inr ⟨len,cap,⟨initial n len cap target cert known⟩,rfl⟩
      · by_cases hi : k ≤ n
        · have eq := (step_unique rel hi b).mp next
          subst b
          exact Or.inr ⟨k+1,by omega,⟨advance rel hi⟩,by omega⟩
        · exact False.elim (halted_at_index (by omega) rel b next)
  exact go path rfl

theorem bounded (n : Nat) {length s} (path : Counted length (before n) s) : length ≤ n+2 := by
  rcases classification n path with ⟨cap,_⟩ | ⟨k,cap,_,eq⟩ <;> omega

theorem halted_outcome (n : Nat) {length t} (path : Counted length (before n) t)
    (noMore : ∀ next, ¬ RawStep t next) :
    length = n+2 ∧
      (∀ fuel, GeneralGeneratedDictionaryRun299.run (table t) fuel 0 =
        if n+1 < fuel then some (dictionary (n+1)) else none) ∧
      ∀ m, Models t m → (boundary roles).Evidence registry t m displayRoot (dictionary (n+1)) := by
  rcases classification n path with ⟨cap,rfl⟩ | ⟨k,cap,⟨rel⟩,eq⟩
  · exact False.elim (noMore _ (GeneralDeferredLadderRefresh302.actual (refPhase n length cap)))
  · by_cases hi : k ≤ n
    · exact False.elim (noMore _ (GeneralDeferredLadderRelay304.step_exists rel hi))
    · exact ⟨by omega,indexed_terminal (by omega) rel⟩

theorem acc_of_bounded (bound : Nat) (s : State roles)
    (limited : ∀ length t, Counted length s t → length ≤ bound) :
    Acc (fun after before => RawStep before after) s := by
  induction bound generalizing s with
  | zero =>
    refine .intro s (fun t step => False.elim ?_)
    have bad := limited 1 t (.tail (.refl s) step)
    omega
  | succ bound ih =>
    refine .intro s (fun t step => ih t ?_)
    intro length endState outgoing
    have seen := limited (1+length) endState
      (GeneralDeferredLadderOutcomes302.append (.tail (.refl s) step) outgoing)
    omega

/-- The actual raw graph from this deferred-ladder source is accessible,
even though it permits infinitely many distinct refresh successors.
This statement is local to this source family. -/
theorem initial_acc (n : Nat) : Acc (fun after before => RawStep before after) (before n) :=
  acc_of_bounded (n+2) (before n) (fun _ _ seen => bounded n seen)

end Yulang.GeneralDeferredLadderClosed304
