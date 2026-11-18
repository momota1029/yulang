import Yulang.GeneralRebaseSourceRequestPool262
import Yulang.GeneralRebaseExecutableRequests262

namespace Yulang.GeneralRebaseDynamicSource262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)

def select (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts plan owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots : State (GeneralRebaseStableClass261.facts plan owner pool) → List (Occurrence roles))
 (state : State (GeneralRebaseStableClass261.facts plan owner pool)) :=
 (roots state).map (GeneralRebaseExecutableRequests262.requests (inspect state))

def observe (plan : Plan roles) (owner : Nat) (pool : List Output) (inspect) (roots) :=
 GeneralRebaseCandidateDriver261.observe plan owner pool (select plan owner pool inspect roots)

theorem covered (plan : Plan roles) (owner : Nat) (pool : List Output) (inspect) (roots)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool) :
 GeneralRebaseCandidateDriver261.Covered plan owner pool (select plan owner pool inspect roots) := by
 intro state outputs member
 obtain ⟨root,_,rfl⟩ := List.mem_map.mp member
 intro output requested
 rw [GeneralRebaseExecutableRequests262.requests_eq] at requested
 exact GeneralRebaseChildRequestPool262.requests_covered _ _ (coverage state) root output requested

theorem completion (plan : Plan roles) (owner : Nat) (pool : List Output) (inspect) (roots)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : State (GeneralRebaseStableClass261.facts plan owner pool)) :
 ∃ after steps, GeneralRebaseSettle259.settle (observe plan owner pool inspect roots) before = .ok after ∧
 GeneralRebaseBudget258.Runs (observe plan owner pool inspect roots) steps before after ∧
 steps ≤ before.remaining.length ∧ (∀ next, ¬ Step (observe plan owner pool inspect roots) after next) :=
 GeneralRebaseCandidateDriver261.completion _ _ _ _ (covered plan owner pool inspect roots coverage) before

/-- The semantic snapshot is the actual one selected at this step. One fixed
Plan supplies fact meanings throughout; changing its capture is not covered. -/
theorem step_actual (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : State (GeneralRebaseStableClass261.facts plan owner pool))
 (step : Step (observe plan owner pool inspect roots) before after) :
 ∃ root ∈ roots before, ∀ assignment,
 GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (inspect before) root plan assignment := by
 obtain ⟨proposal,member,rfl,_⟩ := step
 obtain ⟨outputs,included,rfl⟩ := List.mem_map.mp member
 obtain ⟨root,selected,rfl⟩ := List.mem_map.mp included
 refine ⟨root,selected,?_⟩
 intro assignment
 rw [GeneralRebaseExecutableRequests262.requests_eq]
 exact GeneralRebaseStableClass261.actual_write base plan owner (inspect before) root pool
   (GeneralRebaseChildRequestPool262.requests_covered _ _ (coverage before) root) before assignment
end Yulang.GeneralRebaseDynamicSource262
