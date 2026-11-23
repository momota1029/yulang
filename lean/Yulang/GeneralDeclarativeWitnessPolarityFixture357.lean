import Yulang.GeneralDeclarativeWitnessPointModes357
import Yulang.GeneralDeclarativeWitnessCoverageFixture357
namespace Yulang.GeneralDeclarativeWitnessPolarityFixture357
open GeneralDeclarativeWitnessCoverageFixture357 (prepare)
open GeneralDeclarativeWitnessPointModes357 (read)
open GeneralDeclarativeHead320 (State)
open PresenceNormalForm (Atom)
open CommonNominalConstraints (ArgumentTerm)

def forward : Atom Nat := .tyLe (.var 7) (.var 8)
def backward : Atom Nat := .tyLe (.var 8) (.var 7)
def terms (n : Nat) : List (ArgumentTerm Nat) := [.value (.var n)]
def ordinary (atom : Atom Nat) : State := ⟨⟨[atom],[]⟩,[]⟩

def fixture (key : Nat) (atom : Atom Nat) : Bool :=
  (prepare.map fun e => (read e (ordinary atom) key (terms 7) (terms 8)).isSome).getD false

theorem covariance_emits_actual_forward : fixture 20 forward = true := by decide +kernel
theorem contravariance_emits_actual_backward : fixture 42 backward = true := by decide +kernel
theorem covariance_does_not_accept_reversed_receipt : fixture 20 backward = false := by decide +kernel
theorem contravariance_does_not_accept_reversed_receipt : fixture 42 forward = false := by decide +kernel
theorem nullary_cannot_take_one_value : fixture 90 forward = false := by decide +kernel
theorem no_nominal_at_absent_key : fixture 21 forward = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessPolarityFixture357
