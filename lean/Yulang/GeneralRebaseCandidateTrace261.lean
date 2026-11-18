import Yulang.GeneralRebaseCandidateDriver261
namespace Yulang.GeneralRebaseCandidateTrace261
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

/-- Records actual selected subrequest lists for successful finite writes.
It is an audit witness, not extra runtime journal storage. -/
inductive Trace (plan : Plan roles) (owner : Nat) (candidates : List Output)
 (select : State (GeneralRebaseStableClass261.facts plan owner candidates) → List (List Output)) :
 List (List Output) → State (GeneralRebaseStableClass261.facts plan owner candidates) →
 State (GeneralRebaseStableClass261.facts plan owner candidates) → Prop where
 | nil (state) : Trace plan owner candidates select [] state state
 | next {outputs rest before middle after} : outputs ∈ select before →
   middle = write before (GeneralRebaseStableClass261.facts plan owner outputs) →
   middle.remaining ≠ before.remaining → Trace plan owner candidates select rest middle after →
   Trace plan owner candidates select (outputs :: rest) before after

theorem from_runs (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 {n before after} (run : GeneralRebaseBudget258.Runs
 (GeneralRebaseCandidateDriver261.observe plan owner candidates select) n before after) :
 ∃ history, history.length = n ∧ Trace plan owner candidates select history before after := by
 induction run with
 | nil state => exact ⟨[],rfl,.nil state⟩
 | next step _ ih =>
   obtain ⟨proposal,member,same,progress⟩ := step
   obtain ⟨outputs,selected,rfl⟩ := List.mem_map.mp member
   obtain ⟨rest,length,trace⟩ := ih
   exact ⟨outputs::rest,by simp [length],.next selected same progress trace⟩

theorem to_runs (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 {history before after} (trace : Trace plan owner candidates select history before after) :
 GeneralRebaseBudget258.Runs (GeneralRebaseCandidateDriver261.observe plan owner candidates select)
 history.length before after := by
 induction trace with
 | nil state => exact .nil state
 | next selected same progress _ ih =>
   exact .next ⟨_,List.mem_map.mpr ⟨_,selected,rfl⟩,same,progress⟩ ih

/-- One trace works for all assignments simultaneously. Historical obligations
are retained as conjunctions, rather than reinterpreted at each new subset. -/
theorem models_exact (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (candidates : List Output) (select)
 (covered : GeneralRebaseCandidateDriver261.Covered plan owner candidates select)
 {history before after} (trace : Trace plan owner candidates select history before after) :
 ∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ outputs ∈ history, GeneralRebaseClassTable261.Effects plan outputs assignment := by
 induction trace with
 | nil state => intro assignment; simp
 | @next outputs rest before middle after selected same _ _ ih =>
   intro assignment
   rw [ih]
   have step := GeneralRebaseStableClass261.write_exact base plan owner candidates outputs
     (covered before outputs selected) before assignment
   rw [same]
   rw [step]
   simp only [List.mem_cons,forall_eq_or_imp]
   exact and_assoc

theorem successful_history (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (candidates : List Output) (select)
 (covered : GeneralRebaseCandidateDriver261.Covered plan owner candidates select)
 (before : State (GeneralRebaseStableClass261.facts plan owner candidates)) :
 ∃ after history,
 GeneralRebaseSettle259.settle (GeneralRebaseCandidateDriver261.observe plan owner candidates select) before = .ok after ∧
 Trace plan owner candidates select history before after ∧ history.length ≤ before.remaining.length ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ outputs ∈ history, GeneralRebaseClassTable261.Effects plan outputs assignment) := by
 obtain ⟨after,n,success,run,bound,_⟩ := GeneralRebaseCandidateDriver261.completion plan owner candidates select covered before
 obtain ⟨history,length,trace⟩ := from_runs plan owner candidates select run
 exact ⟨after,history,success,trace,by simpa [length] using bound,models_exact base plan owner candidates select covered trace⟩
end Yulang.GeneralRebaseCandidateTrace261
