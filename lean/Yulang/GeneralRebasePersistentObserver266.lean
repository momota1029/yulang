import Yulang.GeneralRebaseClosedObserver259
import Yulang.GeneralRebaseWriteAlgebra259

namespace Yulang.GeneralRebasePersistentObserver266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseSettle259 (settle)
variable {basis : List Fact}

/-- Progress removes list entries. Sublist refinement retains multiplicities
and order, unlike bare membership inclusion. -/
def Refines (before after : State basis) : Prop := after.remaining.Sublist before.remaining

/-- A proposed fact need only persist while it remains pending; the actual
proposal can be regrouped or reordered. -/
def Persistent (observe : Observer basis) : Prop :=
 ∀ before after, Refines before after →
 ∀ proposal ∈ observe before, ∀ fact ∈ proposal, fact ∈ after.remaining →
   ∃ later ∈ observe after, fact ∈ later

def Terminal (observe : Observer basis) (state : State basis) : Prop :=
 ∀ after, ¬ Step observe state after

theorem step_refines (observe : Observer basis) {before after : State basis}
 (step : Step observe before after) : Refines before after := by
 obtain ⟨proposal,_,rfl,_⟩ := step
 exact List.filter_sublist ..

theorem runs_refine (observe : Observer basis) {before after : State basis} {n : Nat}
 (run : Runs observe n before after) : Refines before after := by
 induction run with
 | nil state => exact List.Sublist.refl _
 | next step _ ih => exact ih.trans (step_refines observe step)

theorem terminal_excludes (observe : Observer basis) (state : State basis)
 (stable : Terminal observe state) (proposal : Proposal) (listed : proposal ∈ observe state) :
 ∀ fact ∈ state.remaining, fact ∉ proposal := by
 apply (GeneralRebaseWriteAlgebra259.fixed_iff state proposal).mp
 by_cases equal : (write state proposal).remaining = state.remaining
 · exact state_ext _ _ equal
 · exact False.elim (stable _ ⟨proposal,listed,rfl,equal⟩)

theorem bounded_step (observe : Observer basis) (persistent : Persistent observe)
 {before after bound : State basis}
 (included : Refines before bound) (stable : Terminal observe bound)
 (step : Step observe before after) : Refines after bound := by
 obtain ⟨proposal,listed,rfl,_⟩ := step
 have unproposed : ∀ fact ∈ bound.remaining, fact ∉ proposal := by
   intro fact pending emitted
   obtain ⟨later,member,forbidden⟩ := persistent before bound included proposal listed fact emitted pending
   exact terminal_excludes observe bound stable later member fact pending forbidden
 have same : bound.remaining.filter (fun fact => !proposal.contains fact) = bound.remaining := by
   apply List.filter_eq_self.mpr
   intro fact pending
   simpa using unproposed fact pending
 have sub := included.filter (fun fact => !proposal.contains fact)
 rw [same] at sub
 exact sub

/-- Every possible run stays below each terminal state that already refines
the start. No scheduling fairness or fixed proposal order is required. -/
theorem bounded_runs (observe : Observer basis) (persistent : Persistent observe)
 {before after bound : State basis} {n : Nat}
 (run : Runs observe n before after) (included : Refines before bound)
 (stable : Terminal observe bound) : Refines after bound := by
 induction run with
 | nil state => exact included
 | next step _ ih => exact ih (bounded_step observe persistent included stable step)

theorem terminal_unique (observe : Observer basis) (persistent : Persistent observe)
 {start first last : State basis} {m n : Nat}
 (run1 : Runs observe m start first) (run2 : Runs observe n start last)
 (firstStable : Terminal observe first) (lastStable : Terminal observe last) : first = last := by
 have one := bounded_runs observe persistent run1 (runs_refine observe run2) lastStable
 have two := bounded_runs observe persistent run2 (runs_refine observe run1) firstStable
 exact state_ext first last (two.eq_of_length_le one.length_le)

/-- Successful scheduler settlement is the least terminal state above the
start, in the sublist refinement order. Closure is only needed for obtaining
a successful run, not for uniqueness among successful runs. -/
theorem settle_minimal (observe : Observer basis) (persistent : Persistent observe)
 {first final bound : State basis}
 (solved : settle observe first = .ok final) (included : Refines first bound)
 (stable : Terminal observe bound) : Refines final bound := by
 obtain ⟨_, run⟩ := GeneralRebaseSettle259.successful_path observe first final solved
 exact bounded_runs observe persistent run included stable

end Yulang.GeneralRebasePersistentObserver266
