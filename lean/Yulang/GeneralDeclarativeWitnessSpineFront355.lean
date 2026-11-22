import Yulang.GeneralDeclarativeWitnessTypedEvidence355
import Yulang.GeneralDeclarativeWitnessCovariantFront353
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSpineFront355
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessCovariantMetadata353 (Input)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line AllParsed all rebuild printRow exact_list)
open GeneralDeclarativeWitnessSpineNode355 (Node Author)
open GeneralDeclarativeWitnessNominalSpine355 (Code Checked classified all_same_model)
open GeneralDeclarativeWitnessTypedRelease354 (Authority Location)
open GeneralDeclarativeWitnessTypedJoint354 (compatible)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeWitnessTypedEvidence355 (Evidence compose)
open GeneralNominalCommonBridge (Assignment)

structure Site where
  authority : Authority
  write : Nat
  nextVersion : Nat
  rows : List Line
  keep : List Nat
  fallback : Nat → Capture

def Site.encode (p : Site) (rs : List Row) : Author :=
  ⟨p.authority,p.write,p.nextVersion,rs,p.keep,p.fallback⟩

inductive Authors (cat : Input) : List Site → List Author → Type where
  | nil : Authors cat [] []
  | cons (someRows : AllParsed cat p.rows rows) :
      Authors cat rest tail → Authors cat (p::rest) (p.encode rows::tail)

def authored (cat : Input) : (ss : List Site) → Option (Σ aa,Authors cat ss aa)
  | [] => some ⟨[],.nil⟩
  | p :: more => do
    let ⟨rows,cert⟩ ← all cat p.rows
    let ⟨later,other⟩ ← authored cat more
    pure ⟨p.encode rows::later,.cons cert other⟩

theorem literal_sites {cat ss aa} (parsed : Authors cat ss aa) :
    aa.map (fun a => a.rows.map printRow) = ss.map Site.rows := by
  induction parsed with
  | nil => rfl
  | cons h rest ih => simp only [List.map_cons,Site.encode,exact_list h,ih]

structure Source where
  problem : Problem
  location : Location
  written : List Line
  routes : List Site

structure Wire where
  entry : GeneralDeclarativeWitnessCovariantInterval353.Wire
  rootReceipt : GeneralDeclarativeWitnessTypedPacket354.Report
  continuation : Code
  report : Report

structure Found (p : Source) (s : State) (w : Wire) where
  root : Node s
  sameProblem : root.input = {p.problem with rows := root.input.rows}
  sameHead : root.head = w.entry
  sameReport : root.out = w.rootReceipt
  rootLocation : root.origin = p.location
  written : AllParsed p.problem.metadata p.written root.input.rows
  rawAuthors : List Author
  authors : Authors p.problem.metadata p.routes rawAuthors
  checked : Checked root
  mentions : compatible checked.rows = true
  exact : agrees ⟨p.problem.metadata.sourceInput,s,p.problem.demand⟩ checked.tree w.report = true

def read (p : Source) (s : State) (w : Wire) : Option (Found p s w) :=
  match built : rebuild p.problem p.written with
  | none => none
  | some binary => do
    let ⟨aa,declared⟩ ← authored p.problem.metadata p.routes
    let verified ← GeneralDeclarativeWitnessTypedRangeWriter354.decode binary.1 w.entry s w.rootReceipt
    let root : Node s := ⟨binary.1,p.location,w.entry,w.rootReceipt,verified⟩
    let all ← GeneralDeclarativeWitnessNominalSpine355.read root aa w.continuation
    if joint : compatible all.rows = true then
      if sign : agrees ⟨p.problem.metadata.sourceInput,s,p.problem.demand⟩ all.tree w.report = true then
        pure ⟨root,GeneralDeclarativeWitnessCovariantFront353.unchanged built,rfl,rfl,rfl,
          binary.2,aa,declared,all,joint,sign⟩
      else none
    else none

theorem exact_sources {p s w} (a : Found p s w) :
    a.root.input.rows.map printRow = p.written ∧
    a.rawAuthors.map (fun d => d.rows.map printRow) = p.routes.map Site.rows :=
  ⟨exact_list a.written,literal_sites a.authors⟩

theorem root_sound {p s w} (a : Found p s w) (m : Assignment) (fit : Models s m) :
    w.report.tree = a.checked.tree ∧
    w.report.result = .selected a.checked.dictionary ∧
    w.report.outputs = p.problem.demand.outputs ∧
    ∃ v, Evidence s m v p.problem.demand a.checked.dictionary := by
  obtain ⟨v,proof⟩ := all_same_model a.checked a.mentions m fit
  have full := compose a.checked m fit v proof
  have changed := congrArg Problem.demand a.sameProblem
  have same : a.root.input.demand = p.problem.demand := changed
  have report := exact_report a.exact
  exact ⟨report.1,report.2.1.trans (classified a.checked),report.2.2,⟨v,same ▸ full⟩⟩

end Yulang.GeneralDeclarativeWitnessSpineFront355
