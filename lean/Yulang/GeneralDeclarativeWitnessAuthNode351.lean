import Yulang.GeneralDeclarativeWitnessRecordNodes350
import Yulang.GeneralDeclarativeWitnessAuthAllocation351
import Yulang.GeneralDeclarativeWitnessRank350
import Yulang.GeneralDeclarativeWitnessCompiler350
import Yulang.GeneralDeclarativeWitnessTaggedBoundary349
import Yulang.GeneralDeclarativeWitnessPointInput349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAuthNode351
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessPointInput349 (PointProblem pick picked)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach support)
open GeneralDeclarativeWitnessReleased350 (Checked project)
open GeneralDeclarativeWitnessAuthAllocation351 (know)
open GeneralDeclarativeWitnessTree349 (Report agrees)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeTaggedElection340 (Head Election)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeWitnessAuthAllocation351 (next used entries)
open GeneralDeclarativeWitnessCompiler350 (Context)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Clause)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂ Resolves)

structure Anchor where
  problem : Problem
  before : State
  manifest : Table
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat

def pointPortal (p : Problem) : PointProblem := ⟨p,0,.emptyRecord⟩

/-- Only the uniquely registered candidate for this role is covered.
An untested competing read is never taken as a negative diagnostic;
rather, this code is outside this specific certificate domain. -/
def waiting {s : State} {manifest : Table} (a : Attached s manifest)
    (r : GeneralDeclarations.Registry) (i : Interpretation) (d : Demand) (impl : Declaration) : Prop :=
  ¬ All₂ (Head (support a) r.constructors i) d.arguments impl.head

theorem replayElection {s : State} {manifest : Table} (a : Attached s manifest)
    {p : Problem} {table : SourceBundle} {decl : Declaration}
    {arg : Capture} {pat : Pattern}
    (args : p.demand.arguments = [arg]) (pattern : decl.head = [pat])
    (chosen : pick (pointPortal p) table = some decl)
    (now : Checked a arg pat)
    (parts : now.fields ≠ [])
    (ready : GeneralDeclarativeWitnessAuthAllocation351.Seen a arg.lower)
    {ranks : GeneralDeclarativeWitnessRank350.Table}
    (ranked : GeneralDeclarativeWitnessRank350.check s ranks = true) :
    Election (support a) (registry table) (interpretation table.snapshot)
      (waiting a (registry table) (interpretation table.snapshot)) p.demand decl := by
  obtain ⟨declared,role,only⟩ := picked chosen
  have heads : All₂ (Head (support a) (registry table).constructors (interpretation table.snapshot))
      p.demand.arguments decl.head := by
    rw [args,pattern]
    exact .cons (GeneralDeclarativeWitnessAuthAllocation351.head now parts _ _) .nil
  constructor
  · intro arg' relevant
    have same : arg' = arg := List.mem_singleton.mp (args ▸ relevant)
    subst arg'
    exact .inl ⟨ready.tag,ready.result⟩
  · exact ⟨_,GeneralDeclarativeWitnessRank350.sound ranked⟩
  · rintro ⟨other,h,test⟩
    cases only other h.1 h.2
    exact test heads
  · exact ⟨⟨declared,role⟩,heads⟩
  · intro other h
    cases only other h.1.1 h.1.2
    rfl

def compilerCtx {p : Anchor} {src : Attached p.before p.manifest} {arg : Capture} {pat : Pattern}
    (source : Checked src arg pat) (table : SourceBundle)
    (decl : Declaration) : Context :=
  ⟨registry table,interpretation table.snapshot,p.problem.demand,decl,next source p.keep,
    used source p.keep,p.keep,p.fallback,p.targets⟩

/-- Per-node sound projection/compilation certificate. With a genuine
election this builds the current C340 local positive step. No child
result is inferred merely from presence of a generated child demand. -/
def selected {p : Anchor} {src : Attached p.before p.manifest} {live : Attached p.problem.state p.manifest}
    {arg : Capture} {pat : Pattern} {table : SourceBundle} {decl : Declaration}
    {w : GeneralDeclarativeWitnessCompiler350.Wire}
    (args : p.problem.demand.arguments = [arg]) (pattern : decl.head = [pat])
    (source : Checked src arg pat)
    (hasGrowth : Extends (next source p.keep) p.problem.state)
    (elected : Election (support live) (registry table) (interpretation table.snapshot)
      (waiting live (registry table) (interpretation table.snapshot)) p.problem.demand decl)
    (compiled : GeneralDeclarativeWitnessCompiler350.Accepted (compilerCtx source table decl) p.problem.state w) :
    Selected (support live) (entries source p.keep) (registry table) (interpretation table.snapshot)
      (waiting live (registry table) (interpretation table.snapshot)) p.problem.demand decl compiled.compiled.kids where
  slice :=
    let grows : Extends p.before p.problem.state := trans
      (GeneralDeclarativeEndpointBatch336.grows ..) hasGrowth
    ⟨p.before,support src,grows,
      ⟨grows.constraints,grows.intervals,fun q h =>
        (GeneralDeclarativeWitnessOrigins350.visible_iff live q).mpr
          ((GeneralDeclarativeWitnessOrigins350.visible_iff src q).mp h)⟩⟩
  keep := p.keep
  named := next source p.keep
  spans := used source p.keep
  reads := entries source p.keep
  input := by
    rw [args,pattern]
    simpa only [List.append_nil] using
      (GeneralDeclarativeTaggedInputs340.Inputs.cons (GeneralDeclarativeWitnessAuthAllocation351.input source p.keep)
        (GeneralDeclarativeTaggedInputs340.Inputs.nil))
  fallback := p.fallback
  targets := p.targets
  ordinary := compiled.compiled.state
  compiler := GeneralDeclarativeWitnessCompiler350.actual compiled
  receipt := GeneralDeclarativeWitnessCompiler350.retained compiled
  retained := fun _ p => p
  elected := elected


open GeneralDeclarativeWitnessRecordReplay350 (Wire)
open GeneralDeclarativeWitnessCompiler350 (Accepted)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessRecordHeader350 (replay)
open GeneralDeclarativeWitnessRecordNodes350 (same_table)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralSourceMetadataBareBundle291 (compile)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)

structure Node {s : State} {t : Table} (live : Attached s t) (table : SourceBundle) (d : Demand) where
  decl : Declaration
  kids : List Demand
  sidecar : List Entry
  selection : Selected (support live) sidecar (registry table) (interpretation table.snapshot)
    (waiting live (registry table) (interpretation table.snapshot)) d decl kids
  fixed : List GeneralDeclarativeHead320.Equation
  meaning : ∀ path, (Fixed.mk path d fixed).Meaning s
  models : ∀ m : Assignment, Models s m → ModelsExact s sidecar m

def replayNode (p : Anchor) {table : SourceBundle}
    (metadata : compile p.problem.source = some table) (live : Attached p.problem.state p.manifest)
    (wire : Wire) : Option (Node live table p.problem.demand) := do
  match header : replay p.problem ⟨p.problem.demand.outputs⟩ with
  | none => none
  | some found =>
    let same : found = table := same_table header metadata
    match chosen : pick (pointPortal p.problem) found with
    | none => none
    | some decl =>
      match ha : p.problem.demand.arguments, hp : decl.head with
      | [arg],[pat] =>
        let original ← attach p.before p.manifest
        let projection ← project original arg pat wire.sourceProjection
        let current ← project live arg pat wire.currentProjection
        let ready ← know live arg.lower wire.readinessRow wire.readinessLink
        if nn : current.fields ≠ [] then
          if rankOK : GeneralDeclarativeWitnessRank350.check p.problem.state wire.ranks = true then
            if a : GeneralDeclarativeWitnessAuthAllocation351.check projection p.keep p.problem.state
                wire.slots wire.projections = true then do
              let compiler ← GeneralDeclarativeWitnessCompiler350.decode
                (compilerCtx projection found decl) p.problem.state wire.emitted
              let fit := GeneralDeclarativeWitnessAuthAllocation351.sound a
              let election := replayElection live ha hp chosen current nn ready rankOK
              let step := selected ha hp projection fit.1 election compiler
              pure ⟨decl,compiler.compiled.kids,entries projection p.keep,same ▸ step,
                wire.emitted.outputRows,
                (fun _ => ⟨by rw [compiler.fixed]; exact GeneralDeclarativeWitnessCompiler350.fixed_targets compiler.run,
                  fun m fit => (GeneralDeclarativeWitnessCompiler350.fixed_in_current compiler m fit).2⟩),
                fit.2.2⟩
            else none
          else none
        else none
      | _,_ => none

end Yulang.GeneralDeclarativeWitnessAuthNode351
