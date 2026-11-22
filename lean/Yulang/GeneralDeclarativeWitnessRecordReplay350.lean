import Yulang.GeneralDeclarativeWitnessOneRecord350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecordReplay350
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessManifest349 (Attached attach support Link)
open GeneralDeclarativeWitnessRecordHead350 (know)
open GeneralDeclarativeWitnessProjection349 (Checked decode)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report classifies)
open GeneralDeclarativeWitnessHeader349 (replay replay_sound)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessOneRecord350 (Anchor pointPortal waiting compilerCtx selected)
open GeneralDeclarativeWitnessPointInput349 (pick)
open GeneralDeclarativeWitnessAllocation350 (entries)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule dictionary_sound)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Resolves Classify Dictionary)

structure Wire where
  sourceProjection : GeneralDeclarativeWitnessRecord349.Wire
  currentProjection : GeneralDeclarativeWitnessRecord349.Wire
  slots : List (Nat × Nat × Nat × Nat)
  projections : List GeneralDeclarativeWitnessExactRest349.Wire
  readinessRow : Nat
  readinessLink : Link
  ranks : GeneralDeclarativeWitnessRank350.Table
  emitted : GeneralDeclarativeWitnessCompiler350.Wire

structure Accepted (p : Anchor) (report : Report) (wire : Wire) where
  table : SourceBundle
  header : replay p.problem ⟨report.outputs⟩ = some table
  decl : Declaration
  onlyCandidate : pick (pointPortal p.problem) table = some decl
  arg : Capture
  args : p.problem.demand.arguments = [arg]
  pat : Pattern
  pattern : decl.head = [pat]
  original : Attached p.before p.manifest
  live : Attached p.problem.state p.manifest
  projection : Checked original arg pat
  now : Checked live arg pat
  nonempty : now.shape ≠ []
  ready : GeneralDeclarativeWitnessRecordHead350.Seen live arg.lower
  ranks : GeneralDeclarativeWitnessRank350.check p.problem.state wire.ranks = true
  allocator : GeneralDeclarativeWitnessAllocation350.check projection p.keep p.problem.state
    wire.slots wire.projections = true
  compiled : GeneralDeclarativeWitnessCompiler350.Accepted (compilerCtx projection table decl)
    p.problem.state wire.emitted

def replayCandidate (p : Anchor) (report : Report) (wire : Wire) :
    Option (Accepted p report wire) := do
  match hr : replay p.problem ⟨report.outputs⟩ with
  | none => none
  | some table =>
    match hc : pick (pointPortal p.problem) table with
    | none => none
    | some decl =>
      match ha : p.problem.demand.arguments, hp : decl.head with
      | [arg],[pat] =>
        let anchored ← attach p.before p.manifest
        let live ← attach p.problem.state p.manifest
        let projection ← decode anchored arg pat wire.sourceProjection
        let now ← decode live arg pat wire.currentProjection
        let ready ← know live arg.lower wire.readinessRow wire.readinessLink
        if nn : now.shape ≠ [] then
          if ranked : GeneralDeclarativeWitnessRank350.check p.problem.state wire.ranks = true then
            if alloc : GeneralDeclarativeWitnessAllocation350.check projection p.keep p.problem.state
                wire.slots wire.projections = true then do
              let compiled ← GeneralDeclarativeWitnessCompiler350.decode (compilerCtx projection table decl)
                p.problem.state wire.emitted
              pure ⟨table,hr,decl,hc,arg,ha,pat,hp,anchored,live,projection,now,nn,ready,ranked,alloc,compiled⟩
            else none
          else none
        else none
      | _,_ => none

def localStep {p : Anchor} {report : Report} {wire : Wire} (a : Accepted p report wire) :
    Selected (support a.live) (entries a.projection p.keep) (registry a.table)
      (interpretation a.table.snapshot) (waiting a.live (registry a.table) (interpretation a.table.snapshot))
      p.problem.demand a.decl a.compiled.compiled.kids :=
  selected a.args a.pattern a.projection (GeneralDeclarativeWitnessAllocation350.sound a.allocator).1
    (GeneralDeclarativeWitnessOneRecord350.replayElection a.live a.args a.pattern a.onlyCandidate a.now a.nonempty a.ready a.ranks)
    a.compiled

abbrev rules {p : Anchor} {report : Report} {wire : Wire} (a : Accepted p report wire) :=
  Rule (support a.live) (entries a.projection p.keep) (registry a.table) (interpretation a.table.snapshot)
    (waiting a.live (registry a.table) (interpretation a.table.snapshot))

/-- Complete positive leaf portal: the actual local replay must have
emitted no children, and the literal solver report must match. -/
def checkLeaf (p : Anchor) (report : Report) (wire : Wire) : Bool :=
  (do
    let a ← replayCandidate p report wire
    pure (a.compiled.compiled.kids.isEmpty && agrees p.problem (.selected a.decl.id []) report) : Option Bool).getD false

theorem leaf {p : Anchor} {report : Report} {wire : Wire} (ok : checkLeaf p report wire = true) :
    ∃ a : Accepted p report wire, report.tree = .selected a.decl.id [] ∧
      report.result = .selected (.node a.decl.id []) ∧ report.outputs = p.problem.demand.outputs ∧
      Classify (rules a) p.problem.demand report.result ∧
      ∀ m : Assignment, Models p.problem.state m →
        Evidence (registry a.table) (interpretation a.table.snapshot) m p.problem.demand (.node a.decl.id []) ∧
        (wire.emitted.outputRows.map GeneralDeclarativeHead320.Equation.left =
          p.problem.demand.outputs.map GeneralSourceState.Output.target ∧
          ∀ e ∈ wire.emitted.outputRows,GeneralDeclarativeEntailment320.Holds m e) := by
  unfold checkLeaf at ok
  cases ran : replayCandidate p report wire with
  | none => simp [ran] at ok
  | some a =>
    rw [ran] at ok
    have parts := GeneralDeclarativeWitnessProblem349.splitAnd
      (show (a.compiled.compiled.kids.isEmpty && agrees p.problem (.selected a.decl.id []) report) = true from ok)
    have noKids := List.isEmpty_iff.mp parts.1
    have step := localStep a
    rw [noKids] at step
    have done : Resolves (rules a) p.problem.demand (.selected a.decl.id []) :=
      .selected (.whole step) .nil
    have solution := exact_report parts.2
    have classification := classifies done parts.2
    obtain ⟨_,checked,coverage,declared,_⟩ := replay_sound a.header
    refine ⟨a,solution.1,solution.2.1,solution.2.2,classification,?_⟩
    rw [solution.2.1] at classification
    intro m fit
    exact ⟨dictionary_sound checked coverage declared classification
      ((GeneralDeclarativeWitnessAllocation350.sound a.allocator).2.2 m fit),
      GeneralDeclarativeWitnessCompiler350.fixed_in_current a.compiled m fit⟩

end Yulang.GeneralDeclarativeWitnessRecordReplay350
