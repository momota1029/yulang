import Yulang.GeneralDeclarativeWitnessGrandchildFixture355
import Yulang.GeneralDeclarativeWitnessGrandchildTree355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeWitnessGrandchildTreeFixture355
open GeneralDeclarativeWitnessGrandchildSeed355 (seed producer)
open GeneralDeclarativeWitnessGrandchildFixture355 (data plan)
open GeneralDeclarativeWitnessGrandchildTree355 (read Checked)
open GeneralDeclarativeWitnessTree349 (Report)

def declared : Report :=
  ⟨.selected 92 [.selected 93 [.selected 94 []]],
    .selected (.node 92 [.node 93 [.node 94 []]]),(producer 10).demand.outputs⟩

def test (report : Report := declared) : Bool :=
  ((data 10).map fun (s,w,k) =>
    ((GeneralDeclarativeWitnessTypedReemit354.decode (seed 10) s w).map fun a =>
      (read a plan k report).isSome).getD false).getD false

theorem actual_three_levels : test = true := by decide +kernel

theorem cannot_flatten_real_tree :
    test {declared with tree := .selected 92 [.selected 93 [],.selected 94 []]} = false := by decide +kernel

theorem cannot_drop_inner_choice :
    test {declared with result := .selected (.node 92 [.node 93 []])} = false := by decide +kernel

theorem cannot_change_root_output_order :
    test {declared with outputs := declared.outputs.reverse} = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessGrandchildTreeFixture355
