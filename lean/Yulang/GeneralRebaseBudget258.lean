import Yulang.GeneralDictionaryRebasePublic258
namespace Yulang.GeneralRebaseBudget258
open GeneralRebaseStep258
variable {basis : List Fact}

inductive Runs (observe : Observer basis) : Nat → State basis → State basis → Prop where
 | nil (state) : Runs observe 0 state state
 | next {n before middle after} : Step observe before middle → Runs observe n middle after →
   Runs observe (n+1) before after

/-- A numeric budget for the new relation, not an old-language step bound. -/
theorem budget (observe : Observer basis) (run : Runs observe n before after) :
 n + after.remaining.length ≤ before.remaining.length := by
 induction run with
 | nil state => simp
 | next step _ ih =>
   have lower := decreases observe step
   omega

theorem source_budget (observe : Observer basis) (run : Runs observe n (initial basis) after) :
 n ≤ basis.length := by
 have bound := budget observe run
 change n + after.remaining.length ≤ basis.length at bound
 omega

theorem idempotent (state : State basis) (proposal : Proposal) :
 write (write state proposal) proposal = write state proposal := by
 apply state_ext
 change (state.remaining.filter _).filter _ = state.remaining.filter _
 rw [List.filter_filter]
 simp only [Bool.and_self]

theorem duplicate_noop (state : State basis) (proposal : Proposal) :
 tryWrite (write state proposal) proposal = none := by
 unfold tryWrite
 rw [idempotent]
 simp

theorem fixture_budget (run : Runs GeneralDictionaryRebaseStep258.observe n
 GeneralDictionaryRebaseStep258.initialState after) : n ≤ 1 := by
 cases run with
 | nil => omega
 | next step rest =>
   have equal := GeneralDictionaryRebaseStep258.first_unique _ step
   subst_vars
   cases rest with
   | nil => omega
   | next second _ => exact False.elim (GeneralDictionaryRebaseStep258.final_stops _ second)
end Yulang.GeneralRebaseBudget258
