import Yulang.GeneralRebaseStableClass261
namespace Yulang.GeneralRebaseCandidateDriver261
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

def observe (plan : Plan roles) (owner : Nat) (candidates : List Output)
 (select : State (GeneralRebaseStableClass261.facts plan owner candidates) → List (List Output)) :
 Observer (GeneralRebaseStableClass261.facts plan owner candidates) :=
 fun state => (select state).map (GeneralRebaseStableClass261.facts plan owner)

/-- Finite candidate coverage of every selected request is a real premise.
It is not inferred from readiness or termination of the generic scheduler. -/
def Covered (plan : Plan roles) (owner : Nat) (candidates : List Output)
 (select : State (GeneralRebaseStableClass261.facts plan owner candidates) → List (List Output)) : Prop :=
 ∀ state outputs, outputs ∈ select state → ∀ output ∈ outputs, output ∈ candidates

theorem closed (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (covered : Covered plan owner candidates select) :
 GeneralRebaseClosedObserver259.Closed (observe plan owner candidates select) := by
 intro state proposal member
 obtain ⟨outputs,included,rfl⟩ := List.mem_map.mp member
 exact GeneralRebaseStableClass261.monotone plan owner outputs candidates (covered state outputs included)

theorem completion (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (covered : Covered plan owner candidates select)
 (state : State (GeneralRebaseStableClass261.facts plan owner candidates)) :
 ∃ final steps, GeneralRebaseSettle259.settle (observe plan owner candidates select) state = .ok final ∧
 GeneralRebaseBudget258.Runs (observe plan owner candidates select) steps state final ∧
 steps ≤ state.remaining.length ∧ (∀ after, ¬ Step (observe plan owner candidates select) final after) :=
 GeneralRebaseClosedObserver259.completion _ (closed plan owner candidates select covered) state

theorem step_exact (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (candidates : List Output) (select) (covered : Covered plan owner candidates select)
 (before after : State (GeneralRebaseStableClass261.facts plan owner candidates))
 (step : Step (observe plan owner candidates select) before after) (assignment : Assignment) :
 ∃ outputs ∈ select before,
 (GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 GeneralRebaseClassTable261.Effects plan outputs assignment) := by
 obtain ⟨proposal,member,rfl,_⟩ := step
 obtain ⟨outputs,included,rfl⟩ := List.mem_map.mp member
 exact ⟨outputs,included,GeneralRebaseStableClass261.write_exact base plan owner candidates outputs
   (covered before outputs included) before assignment⟩

/-- Acc does not require coverage; unsupported proposals can instead error in
checked execution. Neither statement proves a general source observer exists. -/
theorem terminating (plan : Plan roles) (owner : Nat) (candidates : List Output) (select)
 (state : State (GeneralRebaseStableClass261.facts plan owner candidates)) :
 Acc (fun after before => Step (observe plan owner candidates select) before after) state :=
 accessible _ state
end Yulang.GeneralRebaseCandidateDriver261
