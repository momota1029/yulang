import Yulang.GeneralDeclarativeWitnessRecordHead350
import Yulang.GeneralDeclarativeWitnessRank350
import Yulang.GeneralDeclarativeWitnessCompiler350
import Yulang.GeneralDeclarativeWitnessTaggedBoundary349
import Yulang.GeneralDeclarativeWitnessPointInput349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOneRecord350
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessPointInput349 (PointProblem pick picked)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached attach support)
open GeneralDeclarativeWitnessRecordHead350 (know)
open GeneralDeclarativeWitnessTree349 (Report agrees)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeTaggedElection340 (Head Election)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeWitnessAllocation350 (next used entries)
open GeneralDeclarativeWitnessCompiler350 (Context)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Clause)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂ Resolves)

structure Anchor where
  problem : Problem
  before : State
  manifest : Manifest
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat

def pointPortal (p : Problem) : PointProblem := ⟨p,0,.emptyRecord⟩

/-- Only the uniquely registered candidate for this role is covered.
An untested competing read is never taken as a negative diagnostic;
rather, this code is outside this specific certificate domain. -/
def waiting {s : State} {manifest : Manifest} (a : Attached s manifest)
    (r : GeneralDeclarations.Registry) (i : Interpretation) (d : Demand) (impl : Declaration) : Prop :=
  ¬ All₂ (Head (support a) r.constructors i) d.arguments impl.head

theorem replayElection {s : State} {manifest : Manifest} (a : Attached s manifest)
    {p : Problem} {table : SourceBundle} {decl : Declaration}
    {arg : Capture} {pat : Pattern}
    (args : p.demand.arguments = [arg]) (pattern : decl.head = [pat])
    (chosen : pick (pointPortal p) table = some decl)
    (now : GeneralDeclarativeWitnessProjection349.Checked a arg pat)
    (parts : now.shape ≠ [])
    (ready : GeneralDeclarativeWitnessRecordHead350.Seen a arg.lower)
    {ranks : GeneralDeclarativeWitnessRank350.Table}
    (ranked : GeneralDeclarativeWitnessRank350.check s ranks = true) :
    Election (support a) (registry table) (interpretation table.snapshot)
      (waiting a (registry table) (interpretation table.snapshot)) p.demand decl := by
  obtain ⟨declared,role,only⟩ := picked chosen
  have heads : All₂ (Head (support a) (registry table).constructors (interpretation table.snapshot))
      p.demand.arguments decl.head := by
    rw [args,pattern]
    exact .cons (GeneralDeclarativeWitnessRecordHead350.head now parts _ _) .nil
  constructor
  · intro arg' relevant
    have same : arg' = arg := List.mem_singleton.mp (args ▸ relevant)
    subst arg'
    exact .inl ⟨ready.tag,ready.known⟩
  · exact ⟨_,GeneralDeclarativeWitnessRank350.sound ranked⟩
  · rintro ⟨other,h,test⟩
    cases only other h.1 h.2
    exact test heads
  · exact ⟨⟨declared,role⟩,heads⟩
  · intro other h
    cases only other h.1.1 h.1.2
    rfl

def compilerCtx {p : Anchor} {src : Attached p.before p.manifest} {arg : Capture} {pat : Pattern}
    (source : GeneralDeclarativeWitnessProjection349.Checked src arg pat) (table : SourceBundle)
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
    (source : GeneralDeclarativeWitnessProjection349.Checked src arg pat)
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
      ⟨grows.constraints,grows.intervals,fun q h => by
        obtain ⟨o,based,allowed⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp h
        exact (GeneralDeclarativeOrigins321.backed_iff _ _).mpr ⟨o,based,allowed⟩⟩⟩
  keep := p.keep
  named := next source p.keep
  spans := used source p.keep
  reads := entries source p.keep
  input := by
    rw [args,pattern]
    simpa only [List.append_nil] using
      (GeneralDeclarativeTaggedInputs340.Inputs.cons (GeneralDeclarativeWitnessAllocation350.input source p.keep)
        (GeneralDeclarativeTaggedInputs340.Inputs.nil))
  fallback := p.fallback
  targets := p.targets
  ordinary := compiled.compiled.state
  compiler := GeneralDeclarativeWitnessCompiler350.actual compiled
  receipt := GeneralDeclarativeWitnessCompiler350.retained compiled
  retained := fun _ p => p
  elected := elected

end Yulang.GeneralDeclarativeWitnessOneRecord350
