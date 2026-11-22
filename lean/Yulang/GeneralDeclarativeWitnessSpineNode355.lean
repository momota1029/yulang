import Yulang.GeneralDeclarativeWitnessGrandchildTree355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSpineNode355
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessCovariantInterval353 (Wire)
open GeneralDeclarativeWitnessTypedPacket354 (Report At typedAt)
open GeneralDeclarativeWitnessTypedRangeWriter354 (Accepted)
open GeneralDeclarativeWitnessTypedRelease354 (Location Authority Stamp Key position)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeWitnessCompiler350 (portNames printDemand)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

/-- A checked nonpoint-aware compiler receipt at a real occurrence. -/
structure Node (s : State) where
  input : Problem
  origin : Location
  head : Wire
  out : Report
  proof : Accepted input head s out

def Node.ofFirst {i s w} (a : GeneralDeclarativeWitnessTypedReemit354.Linked i s w) (version : Nat) : Node s :=
  ⟨GeneralDeclarativeWitnessTypedChild354.downstream i a.writer.output.state a.child a.out.atWrite.typed.row,
    ⟨i.location.path ++ [i.childOrdinal],version⟩,w.receiverHead,w.receiver,a.receiver⟩

def Node.name {s} (p : Node s) : Nat := p.proof.compiled.readFrom.center.decl.id
def Node.valueName {s} (p : Node s) : Nat := p.proof.compiled.readFrom.center.anchor.current.valueName

def Node.stamp {s} (p : Node s) : Stamp :=
  ⟨p.origin.path,p.input.demand.role,p.name,p.origin.version⟩

def Node.address {s} (p : Node s) (index : Nat) (d : Output) : Key :=
  ⟨p.stamp,index,d.name,d.target⟩

structure Permit {s : State} (p : Node s) (auth : Authority) (ordinal : Nat) where
  item : At p.input p.proof.compiled.readFrom.ctx
    (portNames p.proof.compiled.readFrom.ctx p.proof.compiled.ports).input p.input.demand.outputs ordinal
  found : p.out.trace[ordinal]? = some (.typed item.typed.row)
  capture : item.typed.row.valueName = p.valueName
  controlled : p.stamp ∈ auth.active
  single : (auth.active.map position).Nodup
  grants : p.address ordinal item.demand ∈ auth.released

def release {s : State} (p : Node s) (auth : Authority) (ordinal : Nat) : Option (Permit p auth ordinal) := do
  let r ← typedAt p.proof.compiled.output ordinal
  if current : r.1.typed.row.valueName = p.valueName then
    if active : p.stamp ∈ auth.active then
      if unique : (auth.active.map position).Nodup then
        if key : p.address ordinal r.1.demand ∈ auth.released then
          pure ⟨r.1,p.proof.exact.symm ▸ r.2,current,active,unique,key⟩
        else none
      else none
    else none
  else none

theorem current_payload {s : State} {p : Node s} {auth : Authority} {ordinal : Nat}
    (r : Permit p auth ordinal) (m : Assignment) (fit : Models s m) :
    CommonNominalFullCarrier.Equivalent (m r.item.typed.row.valueName).1
      (.union (m p.proof.compiled.readFrom.center.anchor.first.valueName).1
        (m p.proof.compiled.readFrom.center.anchor.last.valueName).1) := by
  rw [r.capture]
  exact GeneralDeclarativeWitnessCovariantOrigin353.whole_full p.proof.compiled.readFrom.center.anchor m
    (GeneralDeclarativeGrowth327.restrict
      ((GeneralDeclarativeWitnessLiteral349.preserves_iff ..).mp p.proof.kept) m fit)

structure Author where
  authority : Authority
  write : Nat
  nextVersion : Nat
  rows : List Row
  keep : List Nat
  fallback : Nat → Capture

structure Send where
  path : List Nat
  head : Wire
  output : Report

def redirected {s : State} (p : Node s) (a : Author) (d : Demand) (exact : Row) : Problem :=
  { p.input with
    stage := p.proof.compiled.state
    rows := a.rows ++ [exact]
    demand := d
    keep := a.keep
    fallback := a.fallback }

structure Step {s : State} (p : Node s) (a : Author) (w : Send) where
  accepted : Permit p a.authority a.write
  actual : Demand
  only : p.proof.compiled.children = [actual]
  place : w.path = p.origin.path ++ [0]
  clean : accepted.item.typed.row.root ∉ a.rows.map Row.root
  actualRow : w.head.center.center = a.rows.length
  next : Accepted (redirected p a actual accepted.item.typed.row) w.head s w.output

def Step.node {s p a w} (q : @Step s p a w) : Node s :=
  ⟨_,⟨w.path,a.nextVersion⟩,w.head,w.output,q.next⟩

def next {s : State} (p : Node s) (a : Author) (w : Send) : Option (Step p a w) := do
  let permit ← release p a.authority a.write
  match only : p.proof.compiled.children with
  | [d] =>
    if path : w.path = p.origin.path ++ [0] then
      if clean : permit.item.typed.row.root ∉ a.rows.map Row.root then
        if index : w.head.center.center = a.rows.length then do
          let r ← GeneralDeclarativeWitnessTypedRangeWriter354.decode
            (redirected p a d permit.item.typed.row) w.head s w.output
          pure ⟨permit,d,only,path,clean,index,r⟩
        else none
      else none
    else none
  | _ => none

theorem step_exact_row {s : State} {p : Node s} {a w} (q : Step p a w) :
    q.node.proof.compiled.readFrom.center.anchor.current = q.accepted.item.typed.row := by
  have h := q.next.compiled.readFrom.center.anchor.currentAt
  change (a.rows ++ [q.accepted.item.typed.row])[w.head.center.center]? =
    some q.node.proof.compiled.readFrom.center.anchor.current at h
  rw [q.actualRow,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at h
  exact (Option.some.inj h).symm

theorem no_payload_name_renaming {s : State} {p : Node s} {a w} (q : Step p a w) :
    q.node.valueName = p.valueName :=
  (congrArg Row.valueName (step_exact_row q)).trans q.accepted.capture

theorem exact_physical_center {s : State} {p : Node s} {a w} (q : Step p a w) :
    q.node.proof.compiled.readFrom.arg.center = q.accepted.item.demand.target := by
  have h := q.node.proof.compiled.readFrom.center.anchor.actualCenter
  rw [step_exact_row q,GeneralDeclarativeWitnessCovariantInterval353.actual_index] at h
  exact h.symm

theorem joined_edge_same_literal {s : State} {p : Node s} {a w} (q : Step p a w)
    (head : p.proof.compiled.readFrom.center.decl.head = [GeneralDeclarativeWitnessCovariantHead352.rawPattern]) :
    q.accepted.item.demand.target = p.valueName := by
  have d : q.actual ∈ p.proof.compiled.children := by rw [q.only]; exact List.mem_cons_self
  have exactArg : q.node.proof.compiled.readFrom.arg ∈ q.actual.arguments := by
    have shape := q.node.proof.compiled.readFrom.shape
    change q.actual.arguments = [_] at shape
    rw [shape]
    exact List.mem_cons_self
  exact (exact_physical_center q).symm.trans
    (GeneralDeclarativeWitnessRangeCut355.no_grandchild_at_a_different_fixed_target
      p.proof.compiled head d exactArg)

end Yulang.GeneralDeclarativeWitnessSpineNode355
