import Yulang.GeneralDeclarativeWitnessFullIntervals357
import Yulang.GeneralDeclarativeWitnessInheritedModeFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 43000
set_option maxHeartbeats 37000000
namespace Yulang.GeneralDeclarativeWitnessInheritedFullFixture357
open GeneralDeclarativeWitnessCoverageFixture357 (prepare)
open GeneralDeclarativeWitnessInheritedModeFixture357 (wrapped table)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled compile)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives in_current_full_model)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Ty Subtype)
open PresenceNormalForm (Atom)

def key (negative : Bool) : Nat := if negative then 42 else 20
def first (negative : Bool) := wrapped (key negative) 7 8
def last (negative : Bool) := wrapped (key negative) 9 10

def isVariable : Atom Nat → Bool
  | .tyLe (.var _) (.var _) => true
  | _ => false

def verify (negative : Bool) : Bool :=
  (prepare.map fun e =>
    ((compile e table false (first negative) (last negative)).map fun run =>
      decide (run.rows.length = 16) && run.rows.all isVariable).getD false).getD false

theorem exact_inherited_code (negative : Bool) : verify negative = true := by
  cases negative <;> decide +kernel

def chosenModel (t : Ty) : Assignment := fun _ => (t,Common.rowEmpty)

theorem reflexive_in_native_type (t : Ty) {atom : Atom Nat} (vars : isVariable atom = true) :
    atom.Holds CommonNominalFullCarrier.model (chosenModel t) := by
  cases atom with
  | tyLe a b =>
    cases a <;> cases b <;> try cases vars
    exact (eqv_refl t).1
  | rowLe _ _ => cases vars

def compiledState (rows : List (Atom Nat)) : State := ⟨⟨rows,[]⟩,[]⟩

theorem inhabited_native_interval (negative : Bool) (t : Ty) :
    ∃ (e : Environment) (a : Compiled e table false (first negative) (last negative)),
      a.rows.length = 16 ∧
      Models (compiledState a.rows) (chosenModel t) ∧
      ContextDerives table (chosenModel t) false (first negative) (last negative) := by
  have ok := exact_inherited_code negative
  unfold verify at ok
  cases selected : prepare with
  | none => rw [selected] at ok; cases ok
  | some e =>
    rw [selected] at ok
    have yes : ((compile e table false (first negative) (last negative)).map fun run =>
      decide (run.rows.length = 16) && run.rows.all isVariable).getD false = true := ok
    cases compared : compile e table false (first negative) (last negative) with
    | none => rw [compared] at yes; cases yes
    | some run =>
      rw [compared] at yes
      have verify_ : (decide (run.rows.length = 16) && run.rows.all isVariable) = true := yes
      obtain ⟨count,atoms⟩ := GeneralDeclarativeWitnessProblem349.splitAnd verify_
      have current : Models (compiledState run.rows) (chosenModel t) := by
        refine ⟨⟨?_,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩,?_⟩
        · intro a used
          exact reflexive_in_native_type t (List.all_eq_true.mp atoms a used)
        · intro _ impossible
          cases impossible
      exact ⟨e,run,of_decide_eq_true count,current,
        (in_current_full_model run (fun a h => h) (chosenModel t) current).2.2⟩

theorem declared_native_nullary_under_nested_contravariance :
    ∃ (e : Environment) (a : Compiled e table false (first true) (last true)),
      Models (compiledState a.rows) (chosenModel (.nominal 90 [])) ∧
      ContextDerives table (chosenModel (.nominal 90 [])) false (first true) (last true) := by
  obtain ⟨e,a,_,current,sound⟩ := inhabited_native_interval true (.nominal 90 [])
  exact ⟨e,a,current,sound⟩

end Yulang.GeneralDeclarativeWitnessInheritedFullFixture357
