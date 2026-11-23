import Yulang.GeneralDeclarativeWitnessMixedLedger356
import Yulang.GeneralDeclarativeWitnessMixedNestedFixture356
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessMixedLedgerFixture356
open GeneralDeclarativeWitnessMixedLedger356 (Entry Packet read)
open GeneralDeclarativeWitnessMixedNestedFixture356 (Data data checkedRoot report authors)
open GeneralDeclarativeWitnessTypedOutput354 (Write)

def exactLedger : List Entry :=
 [⟨[4],some 7,(1,[(20,20,20)],[(0,5),(1,10),(2,6)]),
    [.typed ⟨5,13,0,10⟩,.typed ⟨10,13,0,10⟩,.ordinary ⟨6,.variable 10⟩]⟩,
  ⟨[4,0],some 8,(3,[(32,10,33)],[]),[]⟩,
  ⟨[4,0,0],none,(5,[(61,10,62)],[(0,70)]),[.ordinary ⟨70,.variant 7 (.variable 126)⟩]⟩,
  ⟨[4,1],none,(4,[(34,10,35)],[(0,60)]),[.ordinary ⟨60,.variant 7 (.variable 86)⟩]⟩]

def packet : Packet := ⟨report,exactLedger⟩
def test (display : List Entry → List Entry := id) : Bool :=
  (data.map (fun d => ((checkedRoot d).map (fun p =>
    (read p d.environment authors d.ordered {packet with outputs := display exactLedger}).isSome)).getD false)).getD false

theorem full_preorder_ledger_is_real : test = true := by decide +kernel

theorem cross_branch_ordinary_output_swap :
    test (fun rows => rows.take 2 ++ (rows.drop 2).reverse) = false := by decide +kernel

def editThird (f : Entry → Entry) : List Entry → List Entry
  | a::b::c::rest => a::b::f c::rest
  | other => other

theorem typo_at_fixed_target_detected :
    test (editThird fun row => {row with writes := [.ordinary ⟨60,.variant 7 (.variable 126)⟩]}) =
      false := by decide +kernel

theorem cannot_claim_nominal_authority_for_ordinary_branch :
    test (editThird fun row => {row with version := some 8}) = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessMixedLedgerFixture356
