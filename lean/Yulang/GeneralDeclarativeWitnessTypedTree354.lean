import Yulang.GeneralDeclarativeWitnessTypedSound354
import Yulang.GeneralDeclarativeWitnessTree349
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedTree354
open GeneralDeclarativeWitnessTypedChild354 (Input Wire Linked)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeHead320 (State)
open CommonRoleOutermostResolver (Tree Dictionary Result classification)
open GeneralDeclarativeDemand320 (Demand)

structure Envelope where
  writerPath : List Nat
  childPath : List Nat
  wire : Wire
  reported : Report

def computed {i s w} (a : Linked i s w) : Tree :=
  .selected a.writer.output.source.decl.id
    [.selected a.receiver.facts.center.decl.id []]

def goal (i : Input) (s : State) : GeneralDeclarativeWitnessProblem349.Problem :=
  ⟨i.producer.metadata.sourceInput,s,i.producer.demand⟩

structure Accepted (i : Input) (s : State) (env : Envelope) where
  core : Linked i s env.wire
  producerAt : env.writerPath = i.location.path
  childAt : env.childPath = i.location.path ++ [i.childOrdinal]
  onlyChild : core.writer.output.children = [core.demand]
  leaf : core.receiver.compiler.compiled.kids = []
  exact : agrees (goal i s) (computed core) env.reported = true

def decode (i : Input) (s : State) (env : Envelope) : Option (Accepted i s env) := do
  let a ← GeneralDeclarativeWitnessTypedChild354.decode i s env.wire
  if head : env.writerPath = i.location.path then
    if path : env.childPath = i.location.path ++ [i.childOrdinal] then
      if kids : a.writer.output.children.map GeneralDeclarativeWitnessCompiler350.printDemand =
          [GeneralDeclarativeWitnessCompiler350.printDemand a.demand] then
        if free : a.receiver.compiler.compiled.kids.isEmpty = true then
          if exact : agrees (goal i s) (computed a) env.reported = true then
            have onlyChild := GeneralDeclarativeWitnessCompiler350.map_injective
              (fun eq => GeneralDeclarativeWitnessCompiler350.print_injective eq) kids
            some ⟨a,head,path,onlyChild,List.isEmpty_iff.mp free,exact⟩
          else none
        else none
      else none
    else none
  else none

theorem exactly {i s e} (a : Accepted i s e) :
    e.reported.tree = computed a.core ∧
    e.reported.result = .selected (.node a.core.writer.output.source.decl.id
      [.node a.core.receiver.facts.center.decl.id []]) ∧
    e.reported.outputs = i.producer.demand.outputs ∧
    e.childPath = e.writerPath ++ [i.childOrdinal] := by
  have printed := exact_report a.exact
  exact ⟨printed.1,printed.2.1,printed.2.2,by rw [a.childAt,a.producerAt]⟩

end Yulang.GeneralDeclarativeWitnessTypedTree354
