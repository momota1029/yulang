import Yulang.GeneralRebaseDriverFixtures259
namespace Yulang.GeneralRebaseWriteAlgebra259
open GeneralRebaseStep258
variable {basis : List Fact}

theorem commute (state : State basis) (first last : Proposal) :
 write (write state first) last = write (write state last) first := by
 apply state_ext
 change (state.remaining.filter _).filter _ = (state.remaining.filter _).filter _
 rw [List.filter_filter,List.filter_filter]
 congr 1
 funext fact
 exact Bool.and_comm _ _

theorem append (state : State basis) (first last : Proposal) :
 write state (first ++ last) = write (write state first) last := by
 apply state_ext
 change state.remaining.filter _ = (state.remaining.filter _).filter _
 rw [List.filter_filter]
 congr 1
 funext fact
 simp [Bool.not_or,Bool.and_comm]

theorem empty (state : State basis) : write state [] = state := by
 apply state_ext
 simp [write]

theorem fixed_iff (state : State basis) (proposal : Proposal) : write state proposal = state ↔
 ∀ fact ∈ state.remaining, fact ∉ proposal := by
 constructor
 · intro same fact member
   have equal := congrArg State.remaining same
   have filtered : fact ∈ (write state proposal).remaining := equal.symm ▸ member
   simpa using (List.mem_filter.mp filtered).2
 · intro missing
   apply state_ext
   change state.remaining.filter _ = state.remaining
   apply List.filter_eq_self.mpr
   intro fact member
   simpa using missing fact member

def batch (state : State basis) : List Proposal → State basis
 | [] => state
 | first :: rest => batch (write state first) rest

theorem batch_exact (state : State basis) (proposals : List Proposal) :
 batch state proposals = write state proposals.flatten := by
 induction proposals generalizing state with
 | nil => exact (empty state).symm
 | cons first rest ih =>
   rw [batch,ih,List.flatten_cons,append]
end Yulang.GeneralRebaseWriteAlgebra259
