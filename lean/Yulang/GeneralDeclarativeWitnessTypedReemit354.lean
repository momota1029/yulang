import Yulang.GeneralDeclarativeWitnessTypedRangeWriter354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedReemit354
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessCovariantOrigin353 (Row View assigned)
open GeneralDeclarativeWitnessTypedPacket354 (Accepted)
open GeneralDeclarativeWitnessTypedRelease354 (Released select)
open GeneralDeclarativeWitnessTypedChild354 (Input downstream)
open GeneralDeclarativeWitnessTypedRangeWriter354 (writes_and_children range_in_same_model)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeWitnessCovariantCanonical353 (valuation rows_at_interval view_for_every_model)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)

structure Wire where
  writerHead : GeneralDeclarativeWitnessCovariantOrigin353.Wire
  writer : GeneralDeclarativeWitnessTypedPacket354.Report
  receiverHead : GeneralDeclarativeWitnessCovariantInterval353.Wire
  receiver : GeneralDeclarativeWitnessTypedPacket354.Report

structure Linked (i : Input) (s : State) (w : Wire) where
  writer : Accepted i.producer w.writerHead s w.writer
  out : Released writer i.location i.auth i.writeOrdinal
  child : Demand
  actual : writer.output.children[i.childOrdinal]? = some child
  ownOrdinal : w.receiverHead.center.center = i.authored.length
  separate : out.atWrite.typed.row.root ∉ i.authored.map Row.root
  receiver : GeneralDeclarativeWitnessTypedRangeWriter354.Accepted
    (downstream i writer.output.state child out.atWrite.typed.row) w.receiverHead s w.receiver

def decode (i : Input) (s : State) (w : Wire) : Option (Linked i s w) := do
  let writer ← GeneralDeclarativeWitnessTypedPacket354.decode i.producer w.writerHead s w.writer
  let out ← select writer i.location i.auth i.writeOrdinal
  match actual : writer.output.children[i.childOrdinal]? with
  | none => none
  | some child =>
    if own : w.receiverHead.center.center = i.authored.length then
      if separate : out.atWrite.typed.row.root ∉ i.authored.map Row.root then do
        let next ← GeneralDeclarativeWitnessTypedRangeWriter354.decode
          (downstream i writer.output.state child out.atWrite.typed.row) w.receiverHead s w.receiver
        pure ⟨writer,out,child,actual,own,separate,next⟩
      else none
    else none

theorem same_released_row {i s w} (a : Linked i s w) :
    a.receiver.compiled.readFrom.center.anchor.current = a.out.atWrite.typed.row := by
  have got := a.receiver.compiled.readFrom.center.anchor.currentAt
  change (i.authored ++ [a.out.atWrite.typed.row])[w.receiverHead.center.center]? =
    some a.receiver.compiled.readFrom.center.anchor.current at got
  rw [a.ownOrdinal,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at got
  exact (Option.some.inj got).symm

theorem released_physical_center {i s w} (a : Linked i s w) :
    a.receiver.compiled.readFrom.arg.center = a.out.atWrite.demand.target := by
  have got := a.receiver.compiled.readFrom.center.anchor.actualCenter
  rw [same_released_row a,GeneralDeclarativeWitnessCovariantInterval353.actual_index] at got
  exact got.symm

theorem scoped_write {i s w} (a : Linked i s w) (m : Assignment) (fit : Models s m) :
    w.receiver.trace.map Write.target = a.child.outputs.map GeneralSourceState.Output.target ∧
    (∀ e ∈ ordinary w.writer.trace,Holds m e) ∧
    (∀ e ∈ a.receiver.compiled.whereRows,Holds m e) ∧
    (∀ e ∈ ordinary w.receiver.trace,Holds m e) :=
  let actual := writes_and_children a.receiver m fit
  ⟨actual.1,(GeneralDeclarativeWitnessTypedPacket354.exact a.writer m fit).2,actual.2.2⟩

def typedView {i s w} (a : Linked i s w) (m : Assignment) :=
  valuation (downstream i a.writer.output.state a.child a.out.atWrite.typed.row) m

theorem carries_original_payload {i s w} (a : Linked i s w) (m : Assignment) (fit : Models s m) :
    ∃ selected : View, typedView a m a.receiver.compiled.readFrom.arg.center = some selected ∧
      selected.tag = a.out.atWrite.typed.row.tag ∧ selected.box = a.out.atWrite.typed.row.box ∧
      Common.Equivalent selected.payload
        (.union (assigned m a.writer.output.source.anchor.first.valueName).1
                (assigned m a.writer.output.source.anchor.last.valueName).1) := by
  obtain ⟨view,atRoot,tag,box,relation⟩ := view_for_every_model
    (downstream i a.writer.output.state a.child a.out.atWrite.typed.row) m
    (rows_at_interval a.receiver.compiled.rangeRead) a.out.atWrite.typed.row
    (List.mem_append_right _ List.mem_cons_self)
  rw [released_physical_center a]
  have ends := GeneralDeclarativeWitnessTypedRelease354.actual_payload a.out m fit
  exact ⟨view,atRoot,tag,box,Common.equivalent_trans relation
    ⟨CommonNominalRegularErasure.subtype_monotone _ _ ends.1,CommonNominalRegularErasure.subtype_monotone _ _ ends.2⟩⟩

end Yulang.GeneralDeclarativeWitnessTypedReemit354
