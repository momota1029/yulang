import Yulang.GeneralRebaseClassCheck261
namespace Yulang.GeneralRebaseClassRun261
open GeneralRebaseStep258
open GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralRebaseClassTable261 (facts)

def observe (plan : Plan roles) (owner : Nat) (outputs : List Output) : Observer (facts plan owner outputs) := fun _ => [facts plan owner outputs]

theorem closed (plan : Plan roles) (owner : Nat) (outputs : List Output) :
 GeneralRebaseClosedObserver259.Closed (observe plan owner outputs) := by
 intro state proposal member
 cases List.mem_singleton.mp member
 exact fun _ included => included

theorem write_all (plan : Plan roles) (owner : Nat) (outputs : List Output) (state : State (facts plan owner outputs)) :
 write state (facts plan owner outputs) = done _ := by
 apply state_ext
 apply List.filter_eq_nil_iff.mpr
 intro fact member
 have inside := state.canonical.subset member
 simpa using inside

inductive Failure where
 | validation (reason : GeneralRebaseClassCheck261.Failure)
 | outside (facts : List Fact)

def run (plan : Plan roles) (owner : Nat) (outputs : List Output) (state : State (facts plan owner outputs)) :
 Except Failure (Option (State (facts plan owner outputs))) :=
 match GeneralRebaseClassCheck261.check plan outputs with
 | .error reason => .error (.validation reason)
 | .ok () =>
   match GeneralRebaseCheckedWrite259.commit state (facts plan owner outputs) with
   | .error outside => .error (.outside outside)
   | .ok result => .ok result

theorem run_exact (plan : Plan roles) (owner : Nat) (outputs : List Output)
 (ready : GeneralRebaseClassCheck261.Ready plan outputs) (state : State (facts plan owner outputs)) :
 run plan owner outputs state = .ok (tryWrite state (facts plan owner outputs)) := by
 unfold run
 rw [(GeneralRebaseClassCheck261.check_exact ..).mpr ready]
 rw [GeneralRebaseCheckedWrite259.supported state _ (fun _ included => included)]

theorem run_step (plan : Plan roles) (owner : Nat) (outputs : List Output)
 (ready : GeneralRebaseClassCheck261.Ready plan outputs) (before after : State (facts plan owner outputs)) :
 run plan owner outputs before = .ok (some after) ↔ Step (observe plan owner outputs) before after := by
 rw [run_exact plan owner outputs ready,Except.ok.injEq,tryWrite_exact]
 simp only [Step,observe,List.mem_singleton,exists_eq_left]

theorem stops (plan : Plan roles) (owner : Nat) (outputs : List Output)
 (ready : GeneralRebaseClassCheck261.Ready plan outputs) : run plan owner outputs (done _) = .ok none := by
 rw [run_exact plan owner outputs ready]
 simp [tryWrite,write_all]

theorem first (plan : Plan roles) (owner : Nat) (outputs : List Output)
 (ready : GeneralRebaseClassCheck261.Ready plan outputs) (nonempty : facts plan owner outputs ≠ []) :
 run plan owner outputs (initial _) = .ok (some (done _)) := by
 rw [run_exact plan owner outputs ready]
 simp [tryWrite,write_all,initial,done,Ne.symm nonempty]

theorem settle_initial (plan : Plan roles) (owner : Nat) (outputs : List Output) :
 GeneralRebaseSettle259.settle (observe plan owner outputs) (initial _) = .ok (done _) := by
 change GeneralRebaseSettle259.settle (fun _ => [facts plan owner outputs]) (initial _) = .ok (done _)
 have result := GeneralRebaseBatchTerminal259.settle_batch (initial (facts plan owner outputs))
   [facts plan owner outputs] (closed plan owner outputs (initial _))
 simpa [observe,GeneralRebaseWriteAlgebra259.batch,write_all] using result

theorem terminating (plan : Plan roles) (owner : Nat) (outputs : List Output) (state : State (facts plan owner outputs)) :
 Acc (fun after before => Step (observe plan owner outputs) before after) state := accessible (observe plan owner outputs) state

/-- Settle is just finite table generation. Readiness is checked by run, and
neither operation checks whether the resulting constraints have a model. -/
theorem done_semantics (base : GeneralNominalCommonBridge.Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (outputs : List Output) (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralRebaseClassTable261.Models base plan owner outputs (done _) assignment ↔
 base assignment ∧ GeneralRebaseClassTable261.Effects plan outputs assignment :=
 GeneralRebaseClassTable261.done_exact ..
end Yulang.GeneralRebaseClassRun261
