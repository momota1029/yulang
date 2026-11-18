import Yulang.GeneralReflexiveDefaultModels260
namespace Yulang.GeneralReflexiveDefaultRun260
open GeneralRebaseStep258
open GeneralReflexiveDefaultSource260 (facts initialState finalState proposal observe)

inductive Failure where
 | decode (reason : GeneralReflexiveDefaultSource260.Failure)
 | outside (facts : List Fact)
 deriving Repr

def run (state : State facts) : Except Failure (Option (State facts)) :=
 match proposal with
 | .error reason => .error (.decode reason)
 | .ok proposed => match GeneralRebaseCheckedWrite259.commit state proposed with
   | .error outside => .error (.outside outside)
   | .ok result => .ok result

theorem run_exact (state : State facts) : run state = .ok (tryWrite state facts) := by
 simp only [run,GeneralReflexiveDefaultSource260.proposal_exact,
   GeneralRebaseCheckedWrite259.supported state facts (List.Subset.refl _)]

theorem run_step (before after : State facts) : run before = .ok (some after) ↔ Step observe before after := by
 rw [run_exact,Except.ok.injEq,GeneralReflexiveDefaultSource260.observe_equal]
 simpa only [GeneralDefaultRebaseRun260.run_exact,Except.ok.injEq] using GeneralDefaultRebaseRun260.run_step before after

theorem first_step : Step observe initialState finalState := by
 rw [GeneralReflexiveDefaultSource260.observe_equal]
 exact GeneralDefaultRebaseSource260.first

theorem first : run initialState = .ok (some finalState) := (run_step ..).mpr first_step

theorem stop : run finalState = .ok none := by rw [run_exact]; rfl

theorem settle_initial : GeneralRebaseSettle259.settle observe initialState = .ok finalState := by
 rw [GeneralReflexiveDefaultSource260.observe_equal]
 exact GeneralDefaultRebaseRun260.settle_initial

theorem one_step_bound (steps : Nat) (state : State facts)
 (path : GeneralRebaseBudget258.Runs observe steps initialState state) : steps ≤ 1 := by
 rw [GeneralReflexiveDefaultSource260.observe_equal] at path
 exact GeneralDefaultRebaseRun260.one_step_bound steps state path
end Yulang.GeneralReflexiveDefaultRun260
