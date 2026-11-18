import Yulang.GeneralOutputRebaseInstalled260
namespace Yulang.GeneralOutputRebaseRun260
open GeneralRebaseStep258
open GeneralOutputRebaseSource260 (facts proposal initialState finalState observe)

inductive Failure where
 | decode (reason : GeneralRebaseOutputDecoder260.Failure)
 | outside (facts : List Fact)
 deriving Repr

/-- Decode coverage and unsupported-basis errors remain errors, not no-ops. -/
def run (state : State facts) : Except Failure (Option (State facts)) :=
 match proposal with
 | .error reason => .error (.decode reason)
 | .ok proposed => match GeneralRebaseCheckedWrite259.commit state proposed with
   | .error outside => .error (.outside outside)
   | .ok result => .ok result

theorem run_exact (state : State facts) : run state = .ok (tryWrite state facts) := by
 simp only [run,GeneralOutputRebaseSource260.proposal_exact,
   GeneralRebaseCheckedWrite259.supported state facts (List.Subset.refl _)]

theorem run_step (before after : State facts) : run before = .ok (some after) ↔ Step observe before after := by
 rw [run_exact,Except.ok.injEq,tryWrite_exact]
 constructor
 · rintro ⟨equal,changed⟩
   exact ⟨facts,by simp [GeneralOutputRebaseSource260.observe_exact],equal,changed⟩
 · rintro ⟨proposed,member,equal,changed⟩
   have same : proposed = facts := by simpa only [GeneralOutputRebaseSource260.observe_exact,List.mem_singleton] using member
   subst proposed
   exact ⟨equal,changed⟩

theorem first : run initialState = .ok (some finalState) :=
 (run_step ..).mpr GeneralOutputRebaseSource260.first

theorem stop : run finalState = .ok none := by rw [run_exact]; rfl

theorem next_exact (state : State facts) : GeneralRebaseScheduler259.next observe state = .ok (tryWrite state facts) := by
 simp only [GeneralRebaseScheduler259.next,GeneralOutputRebaseSource260.observe_exact,
   GeneralRebaseScheduler259.scan,GeneralRebaseCheckedWrite259.supported state facts (List.Subset.refl _)]
 cases tryWrite state facts <;> rfl

theorem settle_initial : GeneralRebaseSettle259.settle observe initialState = .ok finalState := by
 have result := GeneralRebaseBatchTerminal259.settle_batch initialState [facts]
   (by intro p member; cases List.mem_singleton.mp member; exact List.Subset.refl _)
 rw [← GeneralOutputRebaseSource260.observe_exact] at result
 simpa only [GeneralRebaseWriteAlgebra259.batch,GeneralOutputRebaseSource260.write_initial] using result

theorem settle_final : GeneralRebaseSettle259.settle observe finalState = .ok finalState := by
 rw [GeneralRebaseSettle259.settle,next_exact]
 rfl

theorem one_step_bound (steps : Nat) (state : State facts)
 (path : GeneralRebaseBudget258.Runs observe steps initialState state) : steps ≤ 1 := by
 cases path with
 | nil => omega
 | next step tail =>
   obtain ⟨proposed,member,equal,_⟩ := step
   have same : proposed = facts := by simpa only [GeneralOutputRebaseSource260.observe_exact,List.mem_singleton] using member
   subst proposed
   rw [GeneralOutputRebaseSource260.write_initial] at equal
   subst_vars
   cases tail with
   | nil => omega
   | next impossible _ => exact False.elim (GeneralOutputRebaseSource260.stop _ impossible)
end Yulang.GeneralOutputRebaseRun260
