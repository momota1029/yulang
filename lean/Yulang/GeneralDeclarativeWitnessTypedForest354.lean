import Yulang.GeneralDeclarativeWitnessTypedSound354
import Yulang.GeneralDeclarativeWitnessTree349
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedForest354
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row View)
open GeneralDeclarativeWitnessTypedRelease354 (Authority Location)
open GeneralDeclarativeWitnessTypedPacket354 (Report)
open GeneralDeclarativeWitnessTypedChild354 (Linked physical_target)
open GeneralDeclarativeWitnessTypedSound354 (childView released_type_at_actual_center both)
open GeneralDeclarativeWitnessCompiler350 (printDemand print_injective)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Dictionary Result All₂ classifications classification
  classifications_exact classification_exact)
open GeneralDeclarativeWitnessTree349 (agrees exact_report)
open GeneralDeclarativeEntailment320 (Holds)

structure Plan where
  writtenOrdinal : Nat
  authored : List Row
  keep : List Nat
  fallback : Nat → Capture

structure Input where
  producer : Problem
  location : Location
  authority : Authority
  kids : List Plan

def Input.atChild (p : Input) (a : Plan) (n : Nat) : GeneralDeclarativeWitnessTypedChild354.Input :=
  ⟨p.producer,p.location,p.authority,a.writtenOrdinal,n,a.authored,a.keep,a.fallback⟩

structure ChildWire where
  path : List Nat
  head : GeneralDeclarativeWitnessCovariantInterval353.Wire
  body : GeneralDeclarativeWitnessCompiler350.Wire

structure WriterWire where
  head : GeneralDeclarativeWitnessCovariantOrigin353.Wire
  out : Report

def stitch (wr : WriterWire) (child : ChildWire) : GeneralDeclarativeWitnessTypedChild354.Wire :=
  ⟨wr.head,wr.out,child.head,child.body⟩

structure Leaf (p : Input) (s : State) (writer : WriterWire) (idx : Nat) (d : Demand) where
  plan : Plan
  wire : ChildWire
  linked : Linked (p.atChild plan idx) s (stitch writer wire)
  exactDemand : linked.demand = d
  exactPath : wire.path = p.location.path ++ [idx]
  noMore : linked.receiver.compiler.compiled.kids = []

def leaf (p : Input) (s : State) (wr : WriterWire) (idx : Nat) (d : Demand) (plan : Plan) (w : ChildWire) :
    Option (Leaf p s wr idx d) := do
  let linked ← GeneralDeclarativeWitnessTypedChild354.decode (p.atChild plan idx) s (stitch wr w)
  if demand : printDemand linked.demand = printDemand d then
    if path : w.path = p.location.path ++ [idx] then
      if empty : linked.receiver.compiler.compiled.kids.isEmpty = true then
        pure ⟨plan,w,linked,print_injective demand,path,List.isEmpty_iff.mp empty⟩
      else none
    else none
  else none

inductive Leaves (p : Input) (s : State) (wr : WriterWire) : Nat → List Demand → Type where
  | nil : Leaves p s wr i []
  | cons : Leaf p s wr i d → Leaves p s wr (i+1) ds → Leaves p s wr i (d::ds)

def readLeaves (p : Input) (s : State) (wr : WriterWire) (i : Nat) :
    (ds : List Demand) → List Plan → List ChildWire → Option (Leaves p s wr i ds)
  | [],[],[] => some .nil
  | d::ds,plan::more,w::ws => do
    let found ← leaf p s wr i d plan w
    let rest ← readLeaves p s wr (i+1) ds more ws
    pure (.cons found rest)
  | _,_,_ => none

def Leaf.key {p s wr i d} (q : Leaf p s wr i d) := q.linked.receiver.facts.center.decl.id

def Leaves.trees {p s wr i ds} : Leaves p s wr i ds → List Tree
  | .nil => []
  | .cons a rest => .selected a.key [] :: rest.trees

def Leaves.dicts {p s wr i ds} : Leaves p s wr i ds → List Dictionary
  | .nil => []
  | .cons a rest => .node a.key [] :: rest.dicts

theorem Leaves.printed {p s wr i ds} (a : Leaves p s wr i ds) :
    classifications a.trees = a.dicts.map Result.selected := by
  induction a with
  | nil => rfl
  | cons hd tl ih =>
    change _ :: classifications tl.trees = _ :: tl.dicts.map Result.selected
    rw [ih]
    rfl

def BackedNode (s : State) (m : Assignment) (d : Demand) (dictionary : Dictionary) : Prop :=
  ∃ (i : GeneralDeclarativeWitnessTypedChild354.Input) (w : GeneralDeclarativeWitnessTypedChild354.Wire)
    (a : Linked i s w) (seen : View),
    a.demand = d ∧ dictionary = .node a.receiver.facts.center.decl.id [] ∧
    a.receiver.compiler.compiled.kids = [] ∧
    childView a m a.receiver.facts.arg.center = some seen ∧
    seen.box = a.emitted.atWrite.typed.box ∧
    seen.tag = a.emitted.atWrite.typed.tag ∧
    a.receiver.facts.arg.center = a.emitted.atWrite.demand.target ∧
    (∀ e ∈ w.child.outputRows,Holds m e)

theorem Leaves.same_model {p s wr i ds} (a : Leaves p s wr i ds) (m : Assignment) (fit : Models s m) :
    All₂ (BackedNode s m) ds a.dicts := by
  induction a with
  | nil => exact .nil
  | cons hd tl ih =>
    obtain ⟨v,got,tag,box,_⟩ := released_type_at_actual_center hd.linked m fit
    exact .cons ⟨_,_,hd.linked,v,hd.exactDemand,rfl,hd.noMore,got,box,tag,physical_target hd.linked,
      (both hd.linked m fit).2.2.2⟩ ih

structure Wire where
  writer : WriterWire
  children : List ChildWire
  report : GeneralDeclarativeWitnessTree349.Report

structure Accepted (p : Input) (s : State) (w : Wire) where
  parent : GeneralDeclarativeWitnessTypedPacket354.Accepted p.producer w.writer.head s w.writer.out
  children : Leaves p s w.writer 0 parent.output.children
  exact : agrees ⟨p.producer.metadata.sourceInput,s,p.producer.demand⟩
    (.selected parent.output.source.decl.id children.trees) w.report = true

def decode (p : Input) (s : State) (w : Wire) : Option (Accepted p s w) := do
  let r ← GeneralDeclarativeWitnessTypedPacket354.decode p.producer w.writer.head s w.writer.out
  let cs ← readLeaves p s w.writer 0 r.output.children p.kids w.children
  if agree : agrees ⟨p.producer.metadata.sourceInput,s,p.producer.demand⟩
      (.selected r.output.source.decl.id cs.trees) w.report = true then
    pure ⟨r,cs,agree⟩
  else none

theorem exact_model {p s w} (a : Accepted p s w) (m : Assignment) (fit : Models s m) :
    w.report.result = .selected (.node a.parent.output.source.decl.id a.children.dicts) ∧
    w.report.outputs = p.producer.demand.outputs ∧
    All₂ (BackedNode s m) a.parent.output.children a.children.dicts ∧
    (∀ e ∈ GeneralDeclarativeWitnessTypedOutput354.ordinary w.writer.out.trace,Holds m e) := by
  have q := exact_report a.exact
  have out : classification (.selected a.parent.output.source.decl.id a.children.trees) =
      .selected (.node a.parent.output.source.decl.id a.children.dicts) :=
    (classification_exact ..).mpr (.selected ((classifications_exact ..).mp a.children.printed) (.selected rfl))
  exact ⟨q.2.1.trans out,q.2.2,a.children.same_model m fit,
    (GeneralDeclarativeWitnessTypedPacket354.exact a.parent m fit).2⟩

end Yulang.GeneralDeclarativeWitnessTypedForest354
