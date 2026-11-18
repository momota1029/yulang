import Yulang.GeneralRebaseSemanticObserver262
import Yulang.GeneralRebasePlanSemanticExamples262
open Yulang
open GeneralNominalCenters GeneralRebaseStep258
open GeneralRebaseSemanticObserver262
#print axioms observe_eq
#print axioms completion
#print axioms write_actual
#print axioms step_actual

example (fixed : Plan roles) (center) (owner : Nat) (pool : List GeneralSourceState.Output)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (GeneralSourceDictionaries.Occurrence roles))
 (cell : Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
 LayoutCompatible fixed owner pool roots
   (fun _ _ => GeneralRebasePlanSemanticExamples262.recenter fixed center) ∧
 BaseCompatible (fun assignment => assignment = fun _ => cell) fixed owner pool roots
   (fun _ _ => GeneralRebasePlanSemanticExamples262.recenter fixed center) := by
 constructor
 · intro state root selected
   exact ⟨rfl,rfl,rfl⟩
 · intro state root selected assignment equal
   subst assignment
   exact GeneralRebasePlanSemanticExamples262.recenter_compatible fixed center cell
