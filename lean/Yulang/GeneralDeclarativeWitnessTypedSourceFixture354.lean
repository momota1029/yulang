import Yulang.GeneralDeclarativeWitnessTypedForestFixture354
import Yulang.GeneralDeclarativeWitnessTypedSource354

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralDeclarativeWitnessTypedSourceFixture354
open GeneralDeclarativeWitnessTypedForestFixture354 (data problem producer)
open GeneralDeclarativeWitnessTypedSource354 (Source SourcePlan decode)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)

def literal (n payload : Nat) : Line := ⟨n,.variant 13 (.app 0 [.var payload])⟩

def site (second : Bool) : SourcePlan :=
  let left := if second then 34 else 32
  ⟨1,[literal 30 7,literal 31 8,literal left left,literal (left+1) (left+1)],
    [if second then 69 else 49],fun _ => ⟨9,9,9⟩⟩

def source : Source :=
  ⟨{producer with rows := []},problem.location,problem.authority,
    [literal 30 7,literal 31 8,literal 20 9],[site false,site true]⟩

def test (p : Source := source) : Bool :=
  (data.map (fun (s,w) => (decode p s w).isSome)).getD false

theorem literal_author_and_actual_children : test = true := by decide +kernel

theorem stale_cannot_be_author_line :
    test {source with children := [{site false with lines := (site false).lines ++ [literal 9 9]},site true]} =
      false := by decide +kernel

theorem primitive_is_not_covariant :
    test {source with written := [literal 30 7,literal 31 8,⟨20,.variant 13 (.app 1 [.var 9])⟩]} =
      false := by decide +kernel

theorem source_order_not_permutable :
    test {source with children := [site true,site false]} = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTypedSourceFixture354
