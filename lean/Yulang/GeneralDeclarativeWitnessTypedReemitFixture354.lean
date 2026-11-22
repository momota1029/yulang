import Yulang.GeneralDeclarativeWitnessTypedRangeFixture354
import Yulang.GeneralDeclarativeWitnessTypedReemit354
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralDeclarativeWitnessTypedReemitFixture354
open GeneralDeclarativeWitnessTypedRangeFixture354 (producer emitted)
open GeneralDeclarativeWitnessTypedForestFixture354 (problem plan head)
open GeneralDeclarativeWitnessCovariantFixture353 (wire)
open GeneralDeclarativeWitnessTypedChild354 (Input)
open GeneralDeclarativeWitnessTypedReemit354 (Wire decode)
open GeneralDeclarativeWitnessTypedOutput354 (Write)

def seed : Input := {problem.atChild (plan false) 0 with producer := producer}

def test (p : Input := seed) (edit : Wire → Wire := id) : Bool :=
  (emitted.map (fun (s,_,top,child) =>
    (decode p s (edit ⟨wire,top,head false,child⟩)).isSome)).getD false

theorem genuine_released_nonpoint_emits_checked_output : test = true := by decide +kernel

theorem old_release_not_reusable_by_equal_payload :
    test {seed with writeOrdinal := 0} = false := by decide +kernel

theorem no_reemit_from_stale_parent :
    test {seed with location := {seed.location with version := 6}} = false := by decide +kernel

theorem exact_nested_write :
    test seed (fun w => {w with receiver := {w.receiver with trace := [.typed ⟨9,13,0,9⟩]}}) = false :=
  by decide +kernel

theorem lower_endpoint_is_not_the_released_center :
    test seed (fun w =>
      {w with receiverHead := {w.receiverHead with center := {w.receiverHead.center with center := 2}}}) =
      false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTypedReemitFixture354
