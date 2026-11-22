import Yulang.GeneralDeclarativeWitnessPointEvidence349

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 11000
set_option maxHeartbeats 2500000
namespace Yulang.GeneralDeclarativeWitnessPointReplay349
open GeneralDeclarativeWitnessPointInput349 (PointProblem pick printed anchorChecks lit)
open GeneralDeclarativeWitnessPointEvidence349 (support waiting actual_source choice)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessGround349 (occurs receives receipt)
open GeneralDeclarativeWitnessHeader349 (replay replay_sound)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report classifies)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration Clause)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessNode334 (Witness)
open GeneralDeclarativeWitnessHead334 (full)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeWitnessClassify334 (Rule dictionary_sound)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Dictionary Result Classify Resolves classification)

def runBody (p : PointProblem) (s : SourceBundle) (impl : Declaration) : Option (State × List Demand) :=
  compileBody (registry s) (interpretation s.snapshot) p.problem.demand impl p.problem.state
    [] [] (fun _ => lit p) (fun _ _ => 0)

/-- All proof fields are produced by checking; the caller's manifest
and solver report do not carry this type. -/
structure Accepted (p : PointProblem) (report : Report) where
  table : SourceBundle
  header : replay p.problem ⟨report.outputs⟩ = some table
  impl : Declaration
  selected : pick p table = some impl
  ctorID : Nat
  printedHead : printed p table impl = some ctorID
  anchor : anchorChecks p = true
  noWhere : impl.requirements.isEmpty = true
  ordin : State
  compiled : runBody p table impl = some (ordin,[])
  kept : receives ordin p.problem.state = true
  exactOut : agrees p.problem (.selected impl.id []) report = true

def decode (p : PointProblem) (report : Report) : Option (Accepted p report) :=
  match h : replay p.problem ⟨report.outputs⟩ with
  | none => none
  | some s =>
    match hi : pick p s with
    | none => none
    | some impl =>
      match hc : printed p s impl with
      | none => none
      | some ctor =>
        if hanchor : anchorChecks p = true then
          if hleaf : impl.requirements.isEmpty = true then
            match hb : runBody p s impl with
            | some (stage,[]) =>
              if tested : (receives stage p.problem.state && agrees p.problem (.selected impl.id []) report) = true
                then some ⟨s,h,impl,hi,ctor,hc,hanchor,hleaf,stage,hb,(splitAnd tested).1,(splitAnd tested).2⟩
                else none
            | _ => none
          else none
        else none

def check (p : PointProblem) (report : Report) : Bool := (decode p report).isSome

theorem obtained {p : PointProblem} {report : Report} (h : check p report = true) :
    Nonempty (Accepted p report) := by
  unfold check at h
  cases dec : decode p report with
  | none => simp [dec] at h
  | some w => exact ⟨w⟩

theorem at_point {p : PointProblem} {report : Report} (a : Accepted p report) :
    occurs p.problem.state p.atName p.kind = true := (splitAnd a.anchor).2

abbrev rules {p : PointProblem} {report : Report} (a : Accepted p report) :=
  Rule (support p (at_point a)) (registry a.table) (interpretation a.table.snapshot)
    (waiting p a.table (at_point a))

def witness {p : PointProblem} {report : Report} (a : Accepted p report) :
    Witness (support p (at_point a)) (registry a.table) (interpretation a.table.snapshot)
      (waiting p a.table (at_point a)) p.problem.demand a.impl [] :=
  ⟨⟨full _,[],fun _ => lit p,fun _ _ => 0,p.problem.state,[],
    actual_source (at_point a) (splitAnd (splitAnd a.anchor).1).1 a.printedHead,
    a.ordin,a.compiled,receipt a.kept⟩,
    choice (at_point a) (splitAnd (splitAnd a.anchor).1).1 (splitAnd (splitAnd a.anchor).1).2
      a.selected a.printedHead⟩

theorem resolves {p : PointProblem} {report : Report} (a : Accepted p report) :
    Resolves (rules a) p.problem.demand (.selected a.impl.id []) :=
  .selected (.selected (witness a)) .nil

theorem result {p : PointProblem} {report : Report} (a : Accepted p report) :
    report.result = .selected (.node a.impl.id []) := (exact_report a.exactOut).2.1

/-- Genuine C334 bridge for the checked point fragment: no replacement
state, model extension, solver history or previously asserted
classification is an input to this theorem. -/
theorem checked_result {p : PointProblem} {report : Report} (a : Accepted p report) :
    report.tree = .selected a.impl.id [] ∧
    report.result = .selected (.node a.impl.id []) ∧ report.outputs = p.problem.demand.outputs ∧
    Classify (rules a) p.problem.demand report.result ∧
    ∀ m : Assignment, Models p.problem.state m →
      Evidence (registry a.table) (interpretation a.table.snapshot) m p.problem.demand (.node a.impl.id []) := by
  have printed := exact_report a.exactOut
  have classified := classifies (resolves a) a.exactOut
  obtain ⟨_,reg,cov,wanted,_⟩ := replay_sound a.header
  refine ⟨printed.1,result a,printed.2.2,classified,?_⟩
  rw [result a] at classified
  exact dictionary_sound reg cov wanted classified

end Yulang.GeneralDeclarativeWitnessPointReplay349
