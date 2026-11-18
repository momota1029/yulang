import Yulang.GeneralRebaseDynamicTrace262
#print axioms Yulang.GeneralRebaseDynamicSource262.covered
#print axioms Yulang.GeneralRebaseDynamicSource262.completion
#print axioms Yulang.GeneralRebaseDynamicSource262.step_actual
#print axioms Yulang.GeneralRebaseSourceObserver262.source_observer
#print axioms Yulang.GeneralRebaseSourceObserver262.source_step_models
#print axioms Yulang.GeneralRebaseDynamicTrace262.from_runs
#print axioms Yulang.GeneralRebaseDynamicTrace262.to_runs
#print axioms Yulang.GeneralRebaseDynamicTrace262.models_exact
#print axioms Yulang.GeneralRebaseDynamicTrace262.certificate
#print axioms Yulang.GeneralRebaseDynamicTrace262.source_certificate
#check @Yulang.GeneralRebaseDynamicTrace262.source_certificate
#check @Yulang.GeneralRebaseDynamicSource262.step_actual
open Yulang GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

/-- Two arbitrary assignments share this same history and intermediate-state
trace. No history is selected separately for each assignment. -/
example (plan : Plan roles) (owner : Nat) (pool : List Output)
 (base : Assignment → Prop) (inspect) (roots)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : State (GeneralRebaseStableClass261.facts plan owner pool)) (one two : Assignment) :
 ∃ after, ∃ history : List (GeneralRebaseDynamicTrace262.Event roles),
 GeneralRebaseDynamicTrace262.Trace plan owner pool inspect roots history before after ∧
 (GeneralRebaseStableClass261.Models base plan owner after one ↔
   GeneralRebaseStableClass261.Models base plan owner before one ∧
   ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.1 event.2 plan one) ∧
 (GeneralRebaseStableClass261.Models base plan owner after two ↔
   GeneralRebaseStableClass261.Models base plan owner before two ∧
   ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.1 event.2 plan two) := by
 obtain ⟨after,history,_,trace,_,_,meaning⟩ := GeneralRebaseDynamicTrace262.certificate base plan owner pool inspect roots coverage before
 exact ⟨after,history,trace,meaning one,meaning two⟩
