import Yulang.GeneralRebaseWriteAlgebra259
namespace Yulang.GeneralRebaseBatchTerminal259
open GeneralRebaseStep258 GeneralRebaseWriteAlgebra259 GeneralRebaseScheduler259
open GeneralRebaseCheckedWrite259 GeneralRebaseSettle259
variable {basis : List Fact}

theorem absorb (state : State basis) (first last : Proposal) (included : first ⊆ last) :
 write (write state first) last = write state last := by
 apply state_ext
 change (state.remaining.filter _).filter _ = state.remaining.filter _
 rw [List.filter_filter]
 congr 1
 funext fact
 by_cases one : fact ∈ first <;> by_cases two : fact ∈ last <;> simp_all
 exact two (included one)

theorem batch_absorb (state : State basis) (proposals : List Proposal) (proposal : Proposal)
 (member : proposal ∈ proposals) : batch (write state proposal) proposals = batch state proposals := by
 rw [batch_exact,batch_exact]
 exact absorb state proposal proposals.flatten (fun _ inside => List.mem_flatten.mpr ⟨proposal,member,inside⟩)

theorem no_write_iff (state : State basis) (proposal : Proposal) :
 tryWrite state proposal = none ↔ write state proposal = state := by
 unfold tryWrite
 split
 · rename_i same
   exact ⟨fun _ => state_ext _ _ same,fun _ => rfl⟩
 · rename_i different
   constructor
   · intro impossible; cases impossible
   · intro same; exact False.elim (different (congrArg State.remaining same))

theorem batch_fixed (state : State basis) (proposals : List Proposal)
 (all : ∀ proposal ∈ proposals, write state proposal = state) : batch state proposals = state := by
 induction proposals with
 | nil => rfl
 | cons first rest ih =>
   rw [batch,all first List.mem_cons_self]
   exact ih (fun proposal member => all proposal (List.mem_cons_of_mem _ member))

theorem terminal_batch (state : State basis) (proposals : List Proposal)
 (stopped : scan state proposals = .ok none) : batch state proposals = state := by
 apply batch_fixed
 intro proposal member
 exact (no_write_iff state proposal).mp
   (((accepted state proposal none).mp ((scan_none state proposals).mp stopped proposal member)).2)

theorem path_absorb (proposals : List Proposal)
 (path : GeneralRebaseBudget258.Runs (fun _ : State basis => proposals) count before after) :
 batch before proposals = batch after proposals := by
 induction path with
 | nil => rfl
 | next step _ ih =>
   obtain ⟨proposal,member,equal,_⟩ := step
   rw [equal] at ih
   exact (batch_absorb _ proposals proposal member).symm.trans ih

/-- Fixed proposal list only: the state-dependent observer case is not a
confluence theorem. Closed lists settle exactly to their simultaneous union. -/
theorem settle_batch (state : State basis) (proposals : List Proposal)
 (closed : ∀ proposal ∈ proposals, proposal ⊆ basis) :
 settle (fun _ => proposals) state = .ok (batch state proposals) := by
 obtain ⟨final,count,success,path,_,_⟩ := GeneralRebaseClosedObserver259.completion
   (fun _ : State basis => proposals) (fun _ proposal member => closed proposal member) state
 have same := path_absorb proposals path
 have stopped := terminal_batch final proposals (successful_terminal _ state final success)
 rw [stopped] at same
 rw [same]
 exact success
end Yulang.GeneralRebaseBatchTerminal259
