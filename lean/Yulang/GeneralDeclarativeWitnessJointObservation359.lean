import Yulang.GeneralDeclarativeWitnessScopedBindings359
import Yulang.GeneralDeclarativeWitnessNominalRecordFixture359
import Yulang.GeneralDeclarativeWitnessVisibleWithoutCenter359
import Yulang.GeneralDeclarativeWitnessSourceEndpoint359

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 49000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralDeclarativeWitnessJointObservation359
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey Frame ScopedComparison run)
open GeneralDeclarativeWitnessNominalRecordFixture359
  (prepared first last route current exactAtoms genuine common_source_model generated_checks_follow_from_authored_base
   aliasedLow aliasedHigh)
open GeneralDeclarativeWitnessVisibleWithoutCenter359 (VisibleAt visible_monotone written_field_is_present)
open GeneralDeclarativeWitnessOpenFixture359 (low high lowAuthored highAuthored)
open GeneralDeclarativeWitnessOpenSpine359 (sem)
open GeneralDeclarativeWitnessSourceEndpoint359 (Witness check check_exact residual_endpoints endpoint_in_model)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeExactDelete337 (subtract)
open CommonNominalFullCarrier (Subtype subtype_trans record Row)
open CommonNominalFullDemand (Environment)

def parentScope : FrameKey := ⟨[5],72,0⟩
def secondScope : FrameKey := ⟨[5,0],72,0⟩
def parentSpan : Capture := ⟨60,61,62⟩
def secondSpan : Capture := ⟨65,67,66⟩
def frames : List Frame :=
  [⟨parentScope,[(80,parentSpan)]⟩,⟨secondScope,[(81,secondSpan)]⟩]

def inspect (negative : Bool) (e : GeneralDeclarativeWitnessConstructorModes357.Environment) :=
  run e table frames false parentScope secondScope first last (route negative 80) (route negative 81)

theorem scoped_literal_full_atoms (negative : Bool) :
    ((prepared negative).bind fun e => (inspect negative e).map fun a => a.proof.rows) = some exactAtoms := by
  cases negative <;> decide +kernel

theorem same_location_wrong_occurrence_still_fails (negative : Bool) :
    ((prepared negative).map fun e =>
      (run e table frames false secondScope parentScope first last (route negative 80)
        (route negative 81)).isSome).getD true = false := by cases negative <;> decide +kernel

def authored : Source := ⟨[lowAuthored,highAuthored,aliasedLow,aliasedHigh]⟩
def firstLo : Witness := .linked low.path
def firstHi : Witness := .linked high.path
def secondLo : Witness := .linked (.chunk [] 60 low.path)
def secondHi : Witness := .linked (.chunk [] 62 high.path)

theorem four_original_sources :
    check authored current 60 firstLo = true ∧ check authored current 62 firstHi = true ∧
    check authored current 65 secondLo = true ∧ check authored current 66 secondHi = true := by decide +kernel

theorem same_exact_endpoints_not_current_self_authorship :
    check ⟨[lowAuthored,highAuthored]⟩ current 65 secondLo = false ∧
    check ⟨[lowAuthored,highAuthored]⟩ current 66 secondHi = false := by decide +kernel

def lo (m : Assignment) := subtract [7] (sem m (firstLo.code 60))
def hi (m : Assignment) := subtract [7] (sem m (firstHi.code 62))

def Window (m : Assignment) (center : Nat) : Prop :=
  (∀ depth rank (env : Environment Row),VisibleAt (m center).1 (depth+1) rank env 7 .trivial) ∧
  Subtype (lo m) (subtract [7] (m center).1) ∧ Subtype (subtract [7] (m center).1) (hi m)

private theorem first_in {m : Assignment} (fit : Models current m) : Window m 61 := by
  have left : Bound current.normal 60 61 := .interval (by decide)
  have right : Bound current.normal 61 62 := .interval (by decide)
  have readL := check_exact.mp four_original_sources.1
  have readR := check_exact.mp four_original_sources.2.1
  have range := residual_endpoints (arg := parentSpan) readL readR ⟨left,right⟩ m fit [7]
  have upper := subtype_trans (bound_sound m fit.1 right) (endpoint_in_model readR m fit).1
  exact ⟨fun _ _ _ => visible_monotone upper (written_field_is_present 7 _ _ _ _ _),range.2.2⟩

private theorem second_in {m : Assignment} (fit : Models current m) : Window m 67 := by
  have left : Bound current.normal 65 67 := .interval (by decide)
  have right : Bound current.normal 67 66 := .interval (by decide)
  have readL := check_exact.mp four_original_sources.2.2.1
  have readR := check_exact.mp four_original_sources.2.2.2
  have range := residual_endpoints (arg := secondSpan) readL readR ⟨left,right⟩ m fit [7]
  have upper := subtype_trans (bound_sound m fit.1 right) (endpoint_in_model readR m fit).1
  exact ⟨fun _ _ _ => visible_monotone upper (written_field_is_present 7 _ _ _ _ _),range.2.2⟩

theorem same_model_nested_and_open_observations (negative : Bool) (m : Assignment)
    (fit : Models current m) :
    ∃ (e : GeneralDeclarativeWitnessConstructorModes357.Environment)
      (a : ScopedComparison e table frames false parentScope secondScope first last
        (route negative 80) (route negative 81)),
      prepared negative = some e ∧ a.proof.rows = exactAtoms ∧
      GeneralDeclarativeWitnessFullIntervals357.ContextDerives table m false a.left.endpoint a.right.endpoint ∧
      Window m 61 ∧ Window m 67 := by
  have ran := scoped_literal_full_atoms negative
  cases world : prepared negative with
  | none => rw [world] at ran; cases ran
  | some e =>
    rw [world] at ran
    change (inspect negative e).map (fun a => a.proof.rows) = _ at ran
    cases final : inspect negative e with
    | none => simp [final] at ran
    | some a =>
      have exactRows : a.proof.rows = exactAtoms := by simpa [final] using ran
      have fitRows atom (member : atom ∈ a.proof.rows) :=
        generated_checks_follow_from_authored_base m fit atom (exactRows ▸ member)
      refine ⟨e,a,rfl,exactRows,?_,first_in fit,second_in fit⟩
      exact (GeneralDeclarativeWitnessScopedBindings359.every_frame_kept a m fitRows).2.2.2.2.2.2.2.2

end Yulang.GeneralDeclarativeWitnessJointObservation359
