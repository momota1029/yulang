import Yulang.GeneralRebaseStableMergeDriver261
namespace Yulang.GeneralRebaseCandidateValidation261
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

inductive Failure where
 | layout (reason : GeneralRebaseClassCheck261.Failure)
 | outside (facts : List Fact)

/-- Validate the entire fixed candidate layout before running the finite
scheduler. An unused unknown candidate can cause an internal layout error;
this is deliberately not a new language-level rejection rule. -/
def finish (plan : Plan roles) (owner : Nat) (candidates : List Output)
 (select : State (GeneralRebaseStableClass261.facts plan owner candidates) → List (List Output))
 (state : State (GeneralRebaseStableClass261.facts plan owner candidates)) :
 Except Failure (State (GeneralRebaseStableClass261.facts plan owner candidates)) :=
 match GeneralRebaseClassCheck261.check plan candidates with
 | .error reason => .error (.layout reason)
 | .ok () => match GeneralRebaseSettle259.settle (GeneralRebaseCandidateDriver261.observe plan owner candidates select) state with
   | .error missing => .error (.outside missing)
   | .ok after => .ok after

theorem ready_selected (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (covered : GeneralRebaseCandidateDriver261.Covered plan owner candidates select)
 (ready : GeneralRebaseClassCheck261.Ready plan candidates)
 (state : State (GeneralRebaseStableClass261.facts plan owner candidates))
 (outputs : List Output) (selected : outputs ∈ select state) :
 GeneralRebaseClassCheck261.Ready plan outputs :=
 fun output included => ready output (covered state outputs selected output included)

theorem success_exact (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (state after : State (GeneralRebaseStableClass261.facts plan owner candidates)) :
 finish plan owner candidates select state = .ok after ↔
 GeneralRebaseClassCheck261.Ready plan candidates ∧
 GeneralRebaseSettle259.settle (GeneralRebaseCandidateDriver261.observe plan owner candidates select) state = .ok after := by
 constructor
 · intro success
   unfold finish at success
   split at success
   · cases success
   · rename_i check
     refine ⟨(GeneralRebaseClassCheck261.check_exact ..).mp check,?_⟩
     split at success
     · cases success
     · rename_i after' result
       cases Except.ok.inj success
       exact result
 · rintro ⟨ready,settled⟩
   simp only [finish,(GeneralRebaseClassCheck261.check_exact ..).mpr ready,settled]

theorem layout_error (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (state : State (GeneralRebaseStableClass261.facts plan owner candidates)) (reason)
 (failed : GeneralRebaseClassCheck261.check plan candidates = .error reason) :
 finish plan owner candidates select state = .error (.layout reason) := by simp [finish,failed]

theorem completion (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (covered : GeneralRebaseCandidateDriver261.Covered plan owner candidates select)
 (ready : GeneralRebaseClassCheck261.Ready plan candidates)
 (state : State (GeneralRebaseStableClass261.facts plan owner candidates)) :
 ∃ after, finish plan owner candidates select state = .ok after := by
 obtain ⟨after,_,settled,_,_,_⟩ := GeneralRebaseCandidateDriver261.completion plan owner candidates select covered state
 exact ⟨after,(success_exact ..).mpr ⟨ready,settled⟩⟩

theorem trace_ready (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (covered : GeneralRebaseCandidateDriver261.Covered plan owner candidates select)
 (ready : GeneralRebaseClassCheck261.Ready plan candidates)
 {history before after} (trace : GeneralRebaseCandidateTrace261.Trace plan owner candidates select history before after) :
 ∀ outputs ∈ history, GeneralRebaseClassCheck261.Ready plan outputs := by
 induction trace with
 | nil => simp
 | next selected _ _ _ ih =>
   intro outputs member
   rcases List.mem_cons.mp member with rfl | prior
   · exact ready_selected plan owner candidates select covered ready _ _ selected
   · exact ih outputs prior

theorem successful_trace (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (candidates : List Output) (select)
 (covered : GeneralRebaseCandidateDriver261.Covered plan owner candidates select)
 (state after : State (GeneralRebaseStableClass261.facts plan owner candidates))
 (success : finish plan owner candidates select state = .ok after) :
 ∃ history, GeneralRebaseCandidateTrace261.Trace plan owner candidates select history state after ∧
 history.length ≤ state.remaining.length ∧
 (∀ outputs ∈ history, GeneralRebaseClassCheck261.Ready plan outputs) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner state assignment ∧
 ∀ outputs ∈ history, GeneralRebaseClassTable261.Effects plan outputs assignment) := by
 obtain ⟨ready,settled⟩ := (success_exact ..).mp success
 obtain ⟨steps,run,bound⟩ := GeneralRebaseSettle259.successful_budget _ state after settled
 obtain ⟨history,length,trace⟩ := GeneralRebaseCandidateTrace261.from_runs plan owner candidates select run
 exact ⟨history,trace,by simpa [length] using bound,
   trace_ready plan owner candidates select covered ready trace,
   GeneralRebaseCandidateTrace261.models_exact base plan owner candidates select covered trace⟩
end Yulang.GeneralRebaseCandidateValidation261
