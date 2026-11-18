import Yulang.GeneralRebaseMultiSelection263
import Yulang.GeneralRebaseValidatedOutcome263
open Yulang GeneralRebaseStep258
namespace DriverReview263
abbrev basis : List Fact := [.installed 0]
def observe : Observer basis := fun _ => [[.installed 0]]
def validate (state : State basis) : Except Nat Unit :=
 if state.remaining.isEmpty then .error 7 else .ok ()
example : GeneralRebaseScheduler259.next observe (initial basis) = .ok (some (done basis)) := by rfl
example : GeneralRebaseValidatedDriver263.run observe validate (initial basis) = .error (.validation 7) := by
 rw [GeneralRebaseValidatedDriver263.run]
 change GeneralRebaseValidatedDriver263.run observe validate (done basis) = .error (.validation 7)
 rw [GeneralRebaseValidatedDriver263.run]
 rfl
example : GeneralRebaseClosedObserver259.Closed observe := by
 intro state proposal member
 cases List.mem_singleton.mp member
 exact fun _ member => member
end DriverReview263
#print axioms Yulang.GeneralRebaseMultiSelection263.check_exact
#print axioms Yulang.GeneralRebaseMultiSelection263.error_selected
#print axioms Yulang.GeneralRebaseValidatedDriver263.successful_trace
#print axioms Yulang.GeneralRebaseValidatedDriver263.certificate
#print axioms Yulang.GeneralRebaseValidatedOutcome263.error_path
#print axioms Yulang.GeneralRebaseValidatedOutcome263.no_outside
#print axioms Yulang.GeneralRebaseValidatedOutcome263.outcome
#check @Yulang.GeneralRebaseValidatedOutcome263.outcome
