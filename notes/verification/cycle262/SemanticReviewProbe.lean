import Yulang.GeneralRebasePlanSemanticExamples262
import Yulang.GeneralRebaseSelectedSafety262
import Yulang.GeneralRebaseSemanticTrace262
#print axioms Yulang.GeneralRebasePlanSemantic262.actual_value
#print axioms Yulang.GeneralRebasePlanSemantic262.facts_eq
#print axioms Yulang.GeneralRebasePlanSemantic262.class_effects
#print axioms Yulang.GeneralRebasePlanSemanticExamples262.strict_weakening
#print axioms Yulang.GeneralRebaseSemanticObserver262.write_actual
#print axioms Yulang.GeneralRebaseSemanticObserver262.step_actual
#print axioms Yulang.GeneralRebaseSemanticTrace262.source_certificate
#print axioms Yulang.GeneralRebaseSelectedSafety262.no_outside
#print axioms Yulang.GeneralRebaseSelectedSafety262.outcome
#check @Yulang.GeneralRebaseSemanticTrace262.source_certificate
#check @Yulang.GeneralRebaseSelectedSafety262.outcome
open Yulang GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)

/-- Compatibility is needed only on the named base, not every assignment.
This arbitrary Plan example does not assert source reachability or Frame. -/
example (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles))
 (center : Fin (roles fixed.input.occurrence.demand.role).arity → Nat)
 (cell : Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
 GeneralRebaseSemanticObserver262.LayoutCompatible fixed owner pool roots
   (fun _ _ => GeneralRebasePlanSemanticExamples262.recenter fixed center) ∧
 GeneralRebaseSemanticObserver262.BaseCompatible (fun assignment => assignment = (fun _ => cell)) fixed owner pool roots
   (fun _ _ => GeneralRebasePlanSemanticExamples262.recenter fixed center) := by
 constructor
 · intro _ _ _
   exact ⟨rfl,rfl,rfl⟩
 · intro _ _ _ assignment inBase
   subst assignment
   exact GeneralRebasePlanSemanticExamples262.recenter_compatible fixed center cell
