import Yulang.GeneralDeclarativeWitnessTypedOutput354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedPacket354
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire Row)
open GeneralDeclarativeWitnessCovariantCompiler353 (Prepared prepare)
open GeneralDeclarativeWitnessTypedOutput354 (Write Typed Item Batch batch ordinary typedRows)
open GeneralDeclarativeWitnessCompiler350 (preparation whereBatch portNames placed printDemand)
open GeneralDeclarativeClauseBatch327 (Port)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWitnessReceipt349 (Plan verify same_model)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

structure Run (p : Problem) (w : Wire) where
  source : Prepared p w
  prepared : State
  ports : List Port
  pre : preparation source.ctx = some (prepared,ports)
  whereRows : List Equation
  whereProof : whereBatch source.ctx ports = some whereRows
  writes : Batch p source.ctx (portNames source.ctx ports).input p.demand.outputs

def run (p : Problem) (w : Wire) : Option (Run p w) := do
  let src ← prepare p w
  match pre : preparation src.ctx with
  | none => none
  | some (s,ports) =>
    match actual : whereBatch src.ctx ports with
    | none => none
    | some sub => do
      let fixed ← batch p src.ctx (portNames src.ctx ports).input p.demand.outputs
      pure ⟨src,s,ports,pre,sub,actual,fixed⟩

def Run.children {p w} (r : Run p w) : List GeneralDeclarativeDemand320.Demand :=
  GeneralDeclarativeEmissionForest322.children r.source.ctx.decl (portNames r.source.ctx r.ports) (placed r.source.ctx r.ports)

def Run.state {p w} (r : Run p w) : State :=
  appendFacts (appendFacts r.prepared r.whereRows) (ordinary r.writes.trace)

structure Report where
  selected : Nat
  kids : List GeneralDeclarativeWitnessCompiler350.DemandCode
  trace : List Write
  receipt : Plan

structure Accepted (p : Problem) (w : Wire) (s : State) (report : Report) where
  output : Run p w
  ran : run p w = some output
  selected : report.selected = output.source.decl.id
  kids : report.kids = output.children.map printDemand
  trace : report.trace = output.writes.trace
  check : verify output.state s report.receipt = true

def decode (p : Problem) (w : Wire) (s : State) (report : Report) : Option (Accepted p w s report) :=
  match actual : run p w with
  | none => none
  | some r =>
    if chosen : report.selected = r.source.decl.id then
      if kids : report.kids = r.children.map printDemand then
        if writes : report.trace = r.writes.trace then
          if kept : verify r.state s report.receipt = true then
            some ⟨r,actual,chosen,kids,writes,kept⟩
          else none
        else none
      else none
    else none

theorem exact {p w s report} (a : Accepted p w s report) (m : Assignment) (model : Models s m) :
    report.trace.map Write.target = p.demand.outputs.map Output.target ∧
    ∀ q ∈ ordinary report.trace,Holds m q := by
  rw [a.trace]
  exact ⟨GeneralDeclarativeWitnessTypedOutput354.trace_targets a.output.writes,
    ((model_append m).mp (same_model a.check m model)).2⟩

structure At (p : Problem) (c : GeneralDeclarativeWitnessCompiler350.Context)
    (input : Nat → GeneralDeclarativeWhere319.Capture) (outs : List Output) (i : Nat) where
  demand : Output
  indexed : outs[i]? = some demand
  typed : Typed p c input demand

def typedAt {p c input outs} (b : Batch p c input outs) (i : Nat) :
    Option {a : At p c input outs i // b.trace[i]? = some (.typed a.typed.row)} :=
  match b,i with
  | .nil,_ => none
  | .cons (.ordinary ..) _,0 => none
  | .cons (.nominal a) _,0 => some ⟨⟨_,rfl,a⟩,rfl⟩
  | .cons _ bs,i+1 => (typedAt bs i).map (fun a => ⟨⟨a.1.demand,a.1.indexed,a.1.typed⟩,a.2⟩)

end Yulang.GeneralDeclarativeWitnessTypedPacket354
