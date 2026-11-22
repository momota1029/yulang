import Yulang.GeneralDeclarativeWitnessGrandchildContinuity355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessGrandchildTree355
open GeneralDeclarativeWitnessGrandchild355 (Plan Wire Accepted)
open GeneralDeclarativeWitnessTypedReemit354 (Linked)
open GeneralDeclarativeWitnessGrandchildContinuity355 (jointly realInterval)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open CommonRoleOutermostResolver (Tree Dictionary classification)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)

def tree {i s w} {a : Linked i s w} {p code} (r : Accepted a p code) : Tree :=
  .selected a.writer.output.source.decl.id
    [.selected a.receiver.compiled.readFrom.center.decl.id [.selected r.results.facts.center.decl.id []]]

def dictionary {i s w} {a : Linked i s w} {p code} (r : Accepted a p code) : Dictionary :=
  .node a.writer.output.source.decl.id
    [.node a.receiver.compiled.readFrom.center.decl.id [.node r.results.facts.center.decl.id []]]

structure Checked {i s w} (a : Linked i s w) (p : Plan) (code : Wire) (report : Report) where
  last : Accepted a p code
  top : a.writer.output.children = [a.child]
  middle : a.receiver.compiled.children = [last.demand]
  qualified : jointly last = true
  exact : agrees ⟨i.producer.metadata.sourceInput,s,i.producer.demand⟩ (tree last) report = true

def read {i s w} (a : Linked i s w) (p : Plan) (code : Wire) (report : Report) :
    Option (Checked a p code report) := do
  let r ← GeneralDeclarativeWitnessGrandchild355.decode a p code
  if fs : a.writer.output.children.map GeneralDeclarativeWitnessCompiler350.printDemand =
        [GeneralDeclarativeWitnessCompiler350.printDemand a.child] then
    if cs : a.receiver.compiled.children.map GeneralDeclarativeWitnessCompiler350.printDemand =
          [GeneralDeclarativeWitnessCompiler350.printDemand r.demand] then
      if joined : jointly r = true then
        if eq : agrees ⟨i.producer.metadata.sourceInput,s,i.producer.demand⟩ (tree r) report = true then
          pure ⟨r,GeneralDeclarativeWitnessCompiler350.map_injective
            GeneralDeclarativeWitnessCompiler350.print_injective fs,
            GeneralDeclarativeWitnessCompiler350.map_injective
            GeneralDeclarativeWitnessCompiler350.print_injective cs,joined,eq⟩
        else none
      else none
    else none
  else none

theorem ordered {i s w} {a : Linked i s w} {p code report} (ok : Checked a p code report) :
    report.tree = tree ok.last ∧ report.result = .selected (dictionary ok.last) ∧
    report.outputs = i.producer.demand.outputs ∧
    a.writer.output.children = [a.child] ∧
    a.receiver.compiled.children = [ok.last.demand] ∧
    ok.last.results.compiler.compiled.kids = [] := by
  have found := exact_report ok.exact
  exact ⟨found.1,found.2.1,found.2.2,ok.top,ok.middle,ok.last.leaf⟩

theorem all_writes {i s w} {a : Linked i s w} {p code report} (ok : Checked a p code report)
    (m : Assignment) (fit : Models s m) :
    (w.writer.trace.map Write.target = i.producer.demand.outputs.map GeneralSourceState.Output.target) ∧
    (w.receiver.trace.map Write.target = a.child.outputs.map GeneralSourceState.Output.target) ∧
    (code.output.outputRows.map GeneralDeclarativeHead320.Equation.left =
      ok.last.demand.outputs.map GeneralSourceState.Output.target) ∧
    (∀ eq ∈ ordinary w.writer.trace,Holds m eq) ∧
    (∀ eq ∈ ordinary w.receiver.trace,Holds m eq) ∧
    (∀ eq ∈ code.output.outputRows,Holds m eq) ∧
    ∃ v, realInterval v a.receiver.compiled.readFrom.arg w.receiverHead.center.box ∧
      realInterval v ok.last.results.facts.arg code.head.center.box := by
  have parent := GeneralDeclarativeWitnessTypedPacket354.exact a.writer m fit
  have mid := GeneralDeclarativeWitnessTypedRangeWriter354.writes_and_children a.receiver m fit
  have leaf := GeneralDeclarativeWitnessGrandchild355.same_model ok.last m fit
  obtain ⟨v,b,c,_,_⟩ := GeneralDeclarativeWitnessGrandchildContinuity355.one_model_one_typed_table
    ok.last ok.qualified m fit
  exact ⟨parent.1,mid.1,leaf.2.1,parent.2,mid.2.2.2,leaf.2.2,⟨v,b,c⟩⟩

end Yulang.GeneralDeclarativeWitnessGrandchildTree355
