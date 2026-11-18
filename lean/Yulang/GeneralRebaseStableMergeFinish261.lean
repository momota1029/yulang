import Yulang.GeneralRebaseCandidateValidation261
namespace Yulang.GeneralRebaseStableMergeFinish261
open GeneralRebaseStep258
open GeneralRebaseMergeRequests261 (candidate outputs)
open GeneralRebaseStableMerge261 (facts initialState finalState)
open GeneralRebaseStableMergeDriver261 (observe proposal)

theorem terminal_final (fixed) (inspect) (state : State (facts fixed))
 (terminal : ∀ after, ¬ Step (observe fixed inspect) state after) : state = finalState fixed := by
 classical
 by_cases same : (finalState fixed).remaining = state.remaining
 · exact state_ext _ _ same.symm
 · apply False.elim
   apply terminal (finalState fixed)
   refine ⟨proposal fixed (inspect state),?_,(GeneralRebaseStableMergeDriver261.write_actual fixed (inspect state) state).symm,same⟩
   simp [observe,GeneralRebaseCandidateDriver261.observe,GeneralRebaseStableMerge261.select,proposal]

theorem settle_exact (fixed) (inspect) (state : State (facts fixed)) :
 GeneralRebaseSettle259.settle (observe fixed inspect) state = .ok (finalState fixed) := by
 obtain ⟨after,_,success,_,_,terminal⟩ := GeneralRebaseStableMerge261.completion fixed inspect state
 have same := terminal_final fixed inspect after terminal
 rwa [same] at success

noncomputable def finish (fixed) (inspect) (state : State (facts fixed)) :=
 GeneralRebaseCandidateValidation261.finish (candidate fixed) 38 outputs
 (GeneralRebaseStableMerge261.select fixed inspect) state

theorem finish_exact (fixed) (inspect) (state : State (facts fixed)) : finish fixed inspect state = .ok (finalState fixed) :=
 (GeneralRebaseCandidateValidation261.success_exact ..).mpr
 ⟨GeneralRebaseMergeRequests261.ready fixed,settle_exact fixed inspect state⟩

/-- A fully validated finite scheduler can construct an inconsistent constraint
state. No satisfiability check or language acceptance is hidden in finish. -/
theorem success_not_satisfiability (fixed) (inspect) :
 finish fixed inspect (initialState fixed) = .ok (finalState fixed) ∧
 ¬ ∃ assignment, GeneralRebaseStableMerge261.Models fixed (finalState fixed) assignment :=
 ⟨finish_exact fixed inspect _,GeneralRebaseStableMerge261.final_uninhabited fixed⟩
end Yulang.GeneralRebaseStableMergeFinish261
