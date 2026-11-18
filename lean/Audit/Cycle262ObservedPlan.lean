import Yulang.GeneralRebaseObservedPlan262
#print axioms Yulang.GeneralRebaseObservedPlan262.observe
#print axioms Yulang.GeneralRebaseObservedPlan262.Compatible
#print axioms Yulang.GeneralRebaseObservedPlan262.observe_eq
#print axioms Yulang.GeneralRebaseObservedPlan262.write_eq
#print axioms Yulang.GeneralRebaseObservedPlan262.step_iff
#print axioms Yulang.GeneralRebaseObservedPlan262.completion
#print axioms Yulang.GeneralRebaseObservedPlan262.step_actual
#check @Yulang.GeneralRebaseObservedPlan262.completion
#check @Yulang.GeneralRebaseObservedPlan262.step_actual

open Yulang GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)

example (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles)) :
 GeneralRebaseObservedPlan262.Compatible fixed owner pool roots (fun _ _ => fixed) := by
 intro _ _ _
 exact ⟨rfl,rfl,rfl,fun _ => rfl,rfl⟩

/-- Plans of roots that are never selected need no structural certificate. -/
example (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → Occurrence roles → Plan roles) :
 GeneralRebaseObservedPlan262.Compatible fixed owner pool (fun _ => []) plans := by
 intro state root impossible
 cases impossible

example (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalCenteredSteps.State roles)
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → Occurrence roles → Plan roles) :
 GeneralRebaseObservedPlan262.observe fixed owner pool inspect (fun _ => []) plans = (fun _ => []) := rfl

example (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles)) :
 GeneralRebaseObservedPlan262.observe fixed owner pool inspect roots (fun _ _ => fixed) =
 GeneralRebaseDynamicSource262.observe fixed owner pool inspect roots := by
 apply GeneralRebaseObservedPlan262.observe_eq
 intro _ _ _
 exact ⟨rfl,rfl,rfl,fun _ => rfl,rfl⟩
