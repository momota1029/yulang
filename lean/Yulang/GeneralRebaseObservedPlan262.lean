import Yulang.GeneralRebasePlanTransport262
import Yulang.GeneralRebaseDynamicSource262

namespace Yulang.GeneralRebaseObservedPlan262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)

/-- Proposals really use the selected observed Plan. The finite state basis
and stored fact meanings are still those of the fixed reference Plan. -/
def observe (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles))
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → Occurrence roles → Plan roles) :
 Observer (GeneralRebaseStableClass261.facts fixed owner pool) :=
 fun state => (roots state).map fun root => GeneralRebaseStableClass261.facts (plans state root) owner
   (GeneralRebaseExecutableRequests262.requests (inspect state) root)

/-- Only plans of selected roots need the structural transport certificate.
No frame, readiness, packet validity or source compiler is implicit here. -/
def Compatible (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles))
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → Occurrence roles → Plan roles) : Prop :=
 ∀ state root, root ∈ roots state → GeneralRebasePlanTransport262.Same fixed (plans state root)

theorem observe_eq (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : Compatible fixed owner pool roots plans) :
 observe fixed owner pool inspect roots plans = GeneralRebaseDynamicSource262.observe fixed owner pool inspect roots := by
 funext state
 unfold observe GeneralRebaseDynamicSource262.observe GeneralRebaseCandidateDriver261.observe
   GeneralRebaseDynamicSource262.select
 rw [List.map_map]
 apply List.map_congr_left
 intro root selected
 exact (GeneralRebasePlanTransport262.facts_eq fixed (plans state root)
   (compatible state root selected) owner _).symm

theorem write_eq (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalCenteredSteps.State roles) (roots) (plans) (compatible : Compatible fixed owner pool roots plans)
 (before : State (GeneralRebaseStableClass261.facts fixed owner pool))
 (root : Occurrence roles) (selected : root ∈ roots before) :
 write before (GeneralRebaseStableClass261.facts (plans before root) owner
   (GeneralRebaseExecutableRequests262.requests (inspect before) root)) =
 write before (GeneralRebaseStableClass261.facts fixed owner
   (GeneralRebaseExecutableRequests262.requests (inspect before) root)) := by
 exact congrArg (write before) (GeneralRebasePlanTransport262.facts_eq fixed (plans before root)
   (compatible before root selected) owner (GeneralRebaseExecutableRequests262.requests (inspect before) root)).symm

theorem step_iff (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : Compatible fixed owner pool roots plans)
 (before after : State (GeneralRebaseStableClass261.facts fixed owner pool)) :
 Step (observe fixed owner pool inspect roots plans) before after ↔
 Step (GeneralRebaseDynamicSource262.observe fixed owner pool inspect roots) before after := by
 rw [observe_eq fixed owner pool inspect roots plans compatible]

theorem completion (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : Compatible fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : State (GeneralRebaseStableClass261.facts fixed owner pool)) :
 ∃ after steps, GeneralRebaseSettle259.settle (observe fixed owner pool inspect roots plans) before = .ok after ∧
 GeneralRebaseBudget258.Runs (observe fixed owner pool inspect roots plans) steps before after ∧
 steps ≤ before.remaining.length ∧ (∀ next, ¬ Step (observe fixed owner pool inspect roots plans) after next) := by
 rw [observe_eq fixed owner pool inspect roots plans compatible]
 exact GeneralRebaseDynamicSource262.completion fixed owner pool inspect roots coverage before

/-- The same selected root witnesses the model equation for all assignments,
using its actually observed Plan. Same is a structural premise, not a proof
that arbitrary changing captures or declarations preserve meaning. -/
theorem step_actual (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : Compatible fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : State (GeneralRebaseStableClass261.facts fixed owner pool))
 (step : Step (observe fixed owner pool inspect roots plans) before after) :
 ∃ root ∈ roots before, ∀ assignment,
 GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (inspect before) root (plans before root) assignment := by
 have fixedStep := (step_iff fixed owner pool inspect roots plans compatible before after).mp step
 obtain ⟨root,selected,meaning⟩ := GeneralRebaseDynamicSource262.step_actual base fixed owner pool
   inspect roots coverage before after fixedStep
 refine ⟨root,selected,?_⟩
 intro assignment
 exact (meaning assignment).trans (and_congr Iff.rfl
   (GeneralRebasePlanTransport262.class_effects fixed (plans before root)
     (compatible before root selected) (inspect before) root assignment))
end Yulang.GeneralRebaseObservedPlan262
