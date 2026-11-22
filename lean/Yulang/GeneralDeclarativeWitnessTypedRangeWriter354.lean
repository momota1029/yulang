import Yulang.GeneralDeclarativeWitnessTypedConservative354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedRangeWriter354
open GeneralDeclarativeWitnessCovariantInterval353 (Wire RangeRead read typed_interval)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Valuation Row HasView)
open GeneralDeclarativeWitnessTypedOutput354 (Write Batch batch ordinary)
open GeneralDeclarativeWitnessCompiler350 (preparation whereBatch portNames placed printDemand)
open GeneralDeclarativeClauseBatch327 (Port)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeWitnessReceipt349 (Plan verify same_model)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

structure Run (p : Problem) (w : Wire) where
  readFrom : RangeRead p w
  rangeRead : read p w = some readFrom
  prepared : State
  ports : List Port
  preparationRun : preparation readFrom.ctx = some (prepared,ports)
  whereRows : List Equation
  whereRun : whereBatch readFrom.ctx ports = some whereRows
  output : Batch p readFrom.ctx (portNames readFrom.ctx ports).input p.demand.outputs

def run (p : Problem) (w : Wire) : Option (Run p w) :=
  match readOK : read p w with
  | none => none
  | some found =>
    match pre : preparation found.ctx with
    | none => none
    | some (state,ports) =>
      match conditions : whereBatch found.ctx ports with
      | none => none
      | some wr => do
        let done ← batch p found.ctx (portNames found.ctx ports).input p.demand.outputs
        pure ⟨found,readOK,state,ports,pre,wr,conditions,done⟩

def Run.children {p w} (r : Run p w) :=
  GeneralDeclarativeEmissionForest322.children r.readFrom.ctx.decl (portNames r.readFrom.ctx r.ports)
    (placed r.readFrom.ctx r.ports)

def Run.state {p w} (r : Run p w) :=
  appendFacts (appendFacts r.prepared r.whereRows) (ordinary r.output.trace)

structure Accepted (p : Problem) (w : Wire) (s : State) (out : GeneralDeclarativeWitnessTypedPacket354.Report) where
  compiled : Run p w
  ran : run p w = some compiled
  kept : preserves p.stage s = true
  selected : out.selected = compiled.readFrom.center.decl.id
  children : out.kids = compiled.children.map printDemand
  exact : out.trace = compiled.output.trace
  verifies : verify compiled.state s out.receipt = true

def decode (p : Problem) (w : Wire) (s : State) (out : GeneralDeclarativeWitnessTypedPacket354.Report) :
    Option (Accepted p w s out) :=
  match actual : run p w with
  | none => none
  | some r =>
    if kept : preserves p.stage s = true then
      if selected : out.selected = r.readFrom.center.decl.id then
        if kids : out.kids = r.children.map printDemand then
          if writes : out.trace = r.output.trace then
            if terms : verify r.state s out.receipt = true then
              some ⟨r,actual,kept,selected,kids,writes,terms⟩
            else none
          else none
        else none
      else none
    else none

theorem writes_and_children {p w s out} (a : Accepted p w s out) (m : Assignment) (fit : Models s m) :
    out.trace.map Write.target = p.demand.outputs.map Output.target ∧
    out.kids = a.compiled.children.map printDemand ∧
    (∀ e ∈ a.compiled.whereRows,Holds m e) ∧
    ∀ e ∈ ordinary out.trace,Holds m e := by
  have model := (model_append m).mp (same_model a.verifies m fit)
  rw [a.exact]
  exact ⟨GeneralDeclarativeWitnessTypedOutput354.trace_targets a.compiled.output,a.children,
    ((model_append m).mp model.1).2,model.2⟩

open GeneralDeclarativeWitnessCovariantOrigin353 (View assigned)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open CommonDeclaredNominalInspection (DeclaredSubtype)

theorem range_in_same_model {p w s out} (a : Accepted p w s out) (m : Assignment) (fit : Models s m)
    (v : Valuation) (written : ∀ row ∈ p.rows, HasView m v row) :
    ∃ l c h : View,
      v a.compiled.readFrom.arg.lower = some l ∧
      v a.compiled.readFrom.arg.center = some c ∧
      v a.compiled.readFrom.arg.upper = some h ∧
      Common.Equivalent c.payload
        (.union (assigned m a.compiled.readFrom.center.anchor.first.valueName).1
                (assigned m a.compiled.readFrom.center.anchor.last.valueName).1) ∧
      DeclaredSubtype (table w.center.box) (View.head l) (View.head c) ∧
      DeclaredSubtype (table w.center.box) (View.head c) (View.head h) :=
  typed_interval a.compiled.readFrom m v (GeneralDeclarativeGrowth327.restrict
    ((preserves_iff ..).mp a.kept) m fit) written

end Yulang.GeneralDeclarativeWitnessTypedRangeWriter354
