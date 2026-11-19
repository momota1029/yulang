import Yulang.GeneralRebasePersistentObserver266

namespace Yulang.GeneralRebasePersistentJoin266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseSettle259 (settle)
open GeneralRebasePersistentObserver266 (Persistent terminal_unique)
variable {basis : List Fact}

theorem runs_append {observe : Observer basis} {m : Nat} {first middle : State basis}
 (initialRun : Runs observe m first middle) :
 ∀ {n : Nat} {last : State basis}, Runs observe n middle last →
   Runs observe (m+n) first last := by
 induction initialRun with
 | nil state =>
   intro n last rest
   simpa only [Nat.zero_add] using rest
 | @next n first middle after firstStep rest ih =>
   intro k last later
   have joined : Runs observe ((n+k)+1) first last := .next firstStep (ih later)
   have same : n+k+1 = n+1+k := by omega
   exact same ▸ joined

/-- A basis-closed pending-persistent observer has a common join for any
two finite runs from the same state, even when proposals depend on state. -/
theorem join (observe : Observer basis)
 (closed : GeneralRebaseClosedObserver259.Closed observe) (persistent : Persistent observe)
 {initial first last : State basis} {m n : Nat}
 (run1 : Runs observe m initial first) (run2 : Runs observe n initial last) :
 ∃ common, (∃ a, Runs observe a first common) ∧ (∃ b, Runs observe b last common) := by
 obtain ⟨one,a,_,path1,_,quiet1⟩ := GeneralRebaseClosedObserver259.completion observe closed first
 obtain ⟨two,b,_,path2,_,quiet2⟩ := GeneralRebaseClosedObserver259.completion observe closed last
 have equal := terminal_unique observe persistent (runs_append run1 path1) (runs_append run2 path2) quiet1 quiet2
 exact ⟨one,⟨a,path1⟩,⟨b,equal.symm ▸ path2⟩⟩

theorem transfer_runs {first last : Observer basis}
 (same : ∀ before after, Step first before after → Step last before after) {n : Nat} {s t : State basis}
 (path : Runs first n s t) : Runs last n s t := by
 induction path with
 | nil state => exact .nil _
 | next step _ ih => exact .next (same _ _ step) ih

/-- The imperative scheduler can pick different list positions, but two
closed observers with the same strict Step relation settle identically
when one observer is pending-persistent. -/
theorem settle_same_relation (one two : Observer basis)
 (closed1 : GeneralRebaseClosedObserver259.Closed one)
 (closed2 : GeneralRebaseClosedObserver259.Closed two)
 (persistent : Persistent one)
 (same : ∀ before after, Step one before after ↔ Step two before after)
 (initial : State basis) : settle one initial = settle two initial := by
 obtain ⟨first,m,result1,run1,_,quiet1⟩ := GeneralRebaseClosedObserver259.completion one closed1 initial
 obtain ⟨last,n,result2,run2,_,quiet2⟩ := GeneralRebaseClosedObserver259.completion two closed2 initial
 have equivalent := transfer_runs (fun before after step => (same before after).mpr step) run2
 have stable : GeneralRebasePersistentObserver266.Terminal one last := by
   intro after step
   exact quiet2 after ((same last after).mp step)
 have equal := terminal_unique one persistent run1 equivalent quiet1 stable
 rw [result1,result2,equal]

end Yulang.GeneralRebasePersistentJoin266
