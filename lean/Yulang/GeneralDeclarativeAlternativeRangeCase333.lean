import Yulang.GeneralDeclarativeAlternativeRangedReplay333
import Yulang.GeneralDeclarativeInlineRangedModels331

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeAlternativeRangeCase333
open GeneralDeclarativeInlineRangedFrame331
open GeneralDeclarativeInlineDecl331 (root registry decl normal normalizedExpr)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeAlternativeView333 (ofTable Index)
open GeneralDeclarativeAlternativeRange333 (Known materialize)
open GeneralDeclarativeAlternativeRanged333 (captureRanged)
open GeneralDeclarativeAlternativeRangedReplay333 (replay)
open GeneralDeclarativeAlternativeRead333 (normalized)
open GeneralDeclarativeAlternativeCapture333 (Captured)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeOrigins321 (restriction from_source)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeStableAssemble329 (merged MergeFacts)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def range : Known sourceState :=
  fun n => if same : n = 3 then some ⟨interval,same.symm,original_bounds⟩ else none

noncomputable def indexed (done : Nat → Prop) : Index (restriction (before done)) :=
  ofTable sourceRows (fun _ h => from_source (before done) ⟨h,rfl⟩) []

theorem original_material :
    materialize range sourceState (point 0) keep normalizedExpr (seen .actual) = some (rebuilt,spans) :=
  rfl

open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair finiteIndex)
open GeneralDeclarativeAlternativeReadComplete333 (read_plan)
open GeneralDeclarativeAlternativeHeads333 (endpoint_plan endpoint)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeNestedBody332 (compileBody)
open CommonRoleOutermostResolver (All₂)

theorem exact_head (done : Nat → Prop) :
    Planned (fun src : Index (restriction (before done)) => Eventually (fun depth =>
      (rebuilt,spans) ∈ captureRanged range src depth catalogue interpretation keep sourceState
        root.arguments decl.head)) := by
  apply (read_plan (original done .actual)).map
  intro src available
  obtain ⟨depth,whereFound⟩ := available
  refine ⟨depth,fun d enough => ?_⟩
  change _ ∈ captureRanged range src d catalogue interpretation keep sourceState
    [point 0] [GeneralDeclarativeInlineDecl331.pat]
  simp only [captureRanged,normal]
  refine List.mem_flatMap.mpr ⟨⟨seen .actual,original done .actual⟩,whereFound d enough,?_⟩
  rw [original_material]
  exact List.mem_cons_self

theorem exact_endpoints (done : Nat → Prop) :
    All₂ (Matches (restriction (before done)) catalogue interpretation) root.arguments decl.head :=
  .cons ⟨point_bounded _ _,normalizedExpr,_,_,normal,original done .lower,original done .upper⟩ .nil

abbrev actualChild : Demand := ⟨2,[⟨20,3,21⟩],[⟨1,5⟩]⟩
abbrev mergedHead := (merged rebuilt keep spans fallback).state
abbrev parent := appendFacts mergedHead [rootWrite]

theorem concrete_body :
    compileBody registry interpretation root decl rebuilt spans keep fallback targets =
      some (parent,[actualChild]) := rfl

theorem exact_compiler (done : Nat → Prop) :
    Planned (fun src : Index (restriction (before done)) => Eventually (fun depth =>
      (parent,[actualChild]) ∈ replay sourceState range src depth registry interpretation root decl
        keep fallback targets)) := by
  apply ((endpoint_plan (exact_endpoints done)).both (exact_head done)).map
  intro src both
  obtain ⟨least,proved⟩ := eventually_pair both.1 both.2
  refine ⟨least,fun d enough => ?_⟩
  obtain ⟨ready,seen⟩ := proved d enough
  change _ ∈ replay sourceState range src d registry interpretation root decl keep fallback targets
  unfold replay
  rw [ite_eq_left ready]
  exact List.mem_filterMap.mpr ⟨(rebuilt,spans),seen,concrete_body⟩

theorem exact_frame (done : Nat → Prop) :
    ∃ frame : Frame parent registry interpretation root decl [actualChild], frame.targets = targets := by
  obtain ⟨packet,depth,found⟩ := (exact_compiler done).finite
  refine GeneralDeclarativeAlternativeRangedReplay333.frame_from_replay range (finiteIndex packet)
    GeneralDeclarativeInlineDecl331.checked covered List.mem_cons_self rfl declared (fun a one => ?_)
    (found depth (Nat.le_refl _))
  cases List.mem_singleton.mp one
  exact point_bounded _ _

end Yulang.GeneralDeclarativeAlternativeRangeCase333
