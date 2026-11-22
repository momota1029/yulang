import Yulang.GeneralDeclarativeWitnessTypedRelease354
import Yulang.GeneralDeclarativeWitnessCovariantCanonical353
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedChild354
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessTypedPacket354 (Accepted Report)
open GeneralDeclarativeWitnessTypedRelease354 (Location Authority Released select)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)

structure Input where
  producer : Problem
  location : Location
  auth : Authority
  writeOrdinal : Nat
  childOrdinal : Nat
  authored : List Row
  childKeep : List Nat
  childFallback : Nat → Capture

def downstream (i : Input) (state : State) (child : Demand) (actual : Row) : Problem :=
  {i.producer with stage := state, rows := i.authored ++ [actual], demand := child, keep := i.childKeep, fallback := i.childFallback}

structure Wire where
  writerHead : GeneralDeclarativeWitnessCovariantOrigin353.Wire
  writer : Report
  childHead : GeneralDeclarativeWitnessCovariantInterval353.Wire
  child : GeneralDeclarativeWitnessCompiler350.Wire

structure Linked (i : Input) (s : State) (w : Wire) where
  writer : Accepted i.producer w.writerHead s w.writer
  emitted : Released writer i.location i.auth i.writeOrdinal
  demand : Demand
  atChild : writer.output.children[i.childOrdinal]? = some demand
  readFromOutput : w.childHead.center.center = i.authored.length
  keptSeparate : emitted.atWrite.typed.row.root ∉ i.authored.map Row.root
  receiver : GeneralDeclarativeWitnessCovariantInterval353.Checked
    (downstream i writer.output.state demand emitted.atWrite.typed.row) w.childHead s w.child
  ran : GeneralDeclarativeWitnessCovariantInterval353.decode (downstream i writer.output.state demand emitted.atWrite.typed.row)
    w.childHead s w.child = some receiver

def decode (i : Input) (s : State) (w : Wire) : Option (Linked i s w) := do
  let writer ← GeneralDeclarativeWitnessTypedPacket354.decode i.producer w.writerHead s w.writer
  let emitted ← select writer i.location i.auth i.writeOrdinal
  match actual : writer.output.children[i.childOrdinal]? with
  | none => none
  | some d =>
    if exactOrdinal : w.childHead.center.center = i.authored.length then
      if independent : emitted.atWrite.typed.row.root ∉ i.authored.map Row.root then
        match ran : GeneralDeclarativeWitnessCovariantInterval353.decode
            (downstream i writer.output.state d emitted.atWrite.typed.row) w.childHead s w.child with
        | none => none
        | some receiver => some ⟨writer,emitted,d,actual,exactOrdinal,independent,receiver,ran⟩
      else none
    else none

theorem same_row {i s w} (a : Linked i s w) :
    a.receiver.facts.center.anchor.current = a.emitted.atWrite.typed.row := by
  have seen := a.receiver.facts.center.anchor.currentAt
  change (i.authored ++ [a.emitted.atWrite.typed.row])[w.childHead.center.center]? =
      some a.receiver.facts.center.anchor.current at seen
  rw [a.readFromOutput,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at seen
  exact (Option.some.inj seen).symm

theorem physical_target {i s w} (a : Linked i s w) :
    a.receiver.facts.arg.center = a.emitted.atWrite.demand.target := by
  have verified := a.receiver.facts.center.anchor.actualCenter
  rw [same_row a,GeneralDeclarativeWitnessCovariantInterval353.actual_index] at verified
  exact verified.symm

theorem compiler_child {i s w} (a : Linked i s w) :
    w.writer.kids[i.childOrdinal]? = some (printDemand a.demand) := by
  rw [a.writer.kids,List.getElem?_map,a.atChild]
  rfl

end Yulang.GeneralDeclarativeWitnessTypedChild354
