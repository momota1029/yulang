import Yulang.GeneralDeclarativeAlternativeMixedDecl333

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativeAlternativeMixedCase333
open GeneralDeclarativeAlternativeMixedDecl333
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair finiteIndex)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeRange333 (Known materialize)
open GeneralDeclarativeAlternativeNamedHeads333 (namedEndpoint endpoints_plan bothEndpoints materialSpans)
open GeneralDeclarativeAlternativeMixed333 (argument captureMixed Inputs)
open GeneralDeclarativeAlternativeMixedReplay333 (replay frame_from_replay)
open GeneralDeclarativeAlternativeReadComplete333 (read_plan)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStableAssemble329 (merged)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarations (Clause)

abbrev recRhs : Expr := .record 7 (.variable 3) (.variable 5)
abbrev pair : Expr := .primitive .pair [.variable 11,.variable 12]
abbrev inlineRhs : Expr := .variant 4 pair
abbrev namedRhs : Expr := .variant 4 (.variable 7)
abbrev rows : List Equation :=
  [⟨0,recRhs⟩,⟨2,recRhs⟩,⟨9,recRhs⟩,⟨8,inlineRhs⟩,⟨6,namedRhs⟩,⟨10,namedRhs⟩,⟨7,pair⟩,
   ⟨3,.primitive (.scalar .int) []⟩]
abbrev state : State := ⟨⟨[],[(2,0),(0,9),(6,8),(8,10)]⟩,rows⟩
def support (done : Nat → Prop) : Supported state done :=
  ⟨fun e origin => e ∈ rows ∧ origin = .source,fun known => known.1⟩
theorem storage (done : Nat → Prop) {n rhs} (seen : (⟨n,rhs⟩ : Equation) ∈ rows) :
    (⟨n,rhs⟩ : Equation) ∈ (restriction (support done)).equations :=
  from_source _ ⟨seen,rfl⟩
theorem bounds_one : Bounds state firstArg := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩
theorem bounds_two : Bounds state secondArg := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩
abbrev oldUses (mode : GeneralNominalMaterialization.Mode) : List Occurrence := [⟨0,mode,3⟩,⟨1,mode,5⟩]
abbrev futureUses (mode : GeneralNominalMaterialization.Mode) : List Occurrence := [⟨3,mode,11⟩,⟨4,mode,12⟩]
abbrev inlineUses : List GeneralDeclarativeTermWalk322.Occurrence :=
  [⟨3,.actual,.variable 11⟩,⟨4,.actual,.variable 12⟩]
theorem named_record (done : Nat → Prop) (mode) (seen : (⟨n,recRhs⟩ : Equation) ∈ rows) :
    Trace (restriction (support done)) mode n firstCode (oldUses mode) :=
  .record (alias_refl _) (storage done seen) .capture .capture
theorem named_variant (done : Nat → Prop) (mode) (seen : (⟨n,namedRhs⟩ : Equation) ∈ rows) :
    Trace (restriction (support done)) mode n secondCode (futureUses mode) :=
  .variant (alias_refl _) (storage done seen) (.primitive (args := [11,12]) (alias_refl _)
    (storage done (by
      change (⟨7,pair⟩ : Equation) ∈ rows
      simp only [rows,List.mem_cons,List.not_mem_nil,or_false]
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inl trivial))))))))
    (.cons .capture (.cons .capture .nil)))

theorem actual_inline (done : Nat → Prop) :
    Read (restriction (support done)) .actual (.variable 8) secondCode inlineUses := by
  refine .expose (by intro n clash; cases clash) (alias_refl _) (storage done ?_)
    (.variant (.primitive (.cons .capture (.cons .capture .nil))))
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem actual_modes (done : Nat → Prop) :
    Inputs (support done) constructors interpretation root.arguments decl.head :=
  .cons ⟨bounds_one,.inl ⟨_,_,normal_first,named_record done .actual List.mem_cons_self⟩⟩
    (.cons ⟨bounds_two,.inr ⟨_,_,normal_second,actual_inline done⟩⟩ .nil)

theorem independent_endpoints (done : Nat → Prop) :
    HeadMatches (restriction (support done)) constructors interpretation root decl := by
  refine .cons ⟨bounds_one,_,_,_,normal_first,named_record done .lower ?_,named_record done .upper ?_⟩
    (.cons ⟨bounds_two,_,_,_,normal_second,named_variant done .lower ?_,named_variant done .upper ?_⟩ .nil)
  all_goals simp only [rows,List.mem_cons,List.not_mem_nil,or_false]
  · exact .inr (.inl trivial)
  · exact .inr (.inr (.inl trivial))
  · exact .inr (.inr (.inr (.inr (.inl trivial))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl trivial)))))

def view : Known state := fun _ => none
abbrev keep := [14]
def fallback (_ : Nat) := point 3
def targets (_ : Clause) (_ : Nat) := 14
abbrev spans : List (Nat × Capture) := [(0,point 3),(1,point 5),(3,point 11),(4,point 12)]
abbrev observed := appendFacts state [⟨8,inlineRhs⟩]
abbrev child : Demand := ⟨2,[⟨15,3,16⟩],[⟨1,14⟩]⟩
abbrev compiled := (merged observed keep spans fallback).state

theorem exact_body :
    compileBody registry interpretation root decl observed spans keep fallback targets =
      some (compiled,[child]) := rfl

theorem exact_head (done : Nat → Prop) :
    Planned (fun src : Index (restriction (support done)) => Eventually (fun f =>
      (observed,spans) ∈ captureMixed view src f constructors interpretation keep state
        root.arguments decl.head)) := by
  have oldPacket := GeneralDeclarativeAlternativeNamedHeads333.read_plan normal_first
    (named_record done .actual (n := 0) List.mem_cons_self)
  apply (oldPacket.both (read_plan (actual_inline done))).map
  intro src known
  obtain ⟨limit,above⟩ := eventually_pair known.1 known.2
  refine ⟨limit,fun f enough => ?_⟩
  have before := (above f enough).1
  have after := (above f enough).2
  change _ ∈ captureMixed view src f constructors interpretation keep state [firstArg,secondArg]
    [first,second]
  have old : (state,[(0,point 3),(1,point 5)]) ∈
      argument view src f constructors interpretation keep state firstArg first :=
    List.mem_append_left _ (List.mem_map.mpr ⟨oldUses .actual,before,rfl⟩)
  have inline : (observed,[(3,point 11),(4,point 12)]) ∈
      argument view src f constructors interpretation keep state secondArg second := by
    apply List.mem_append_right
    rw [normal_second]
    exact List.mem_filterMap.mpr ⟨⟨inlineUses,actual_inline done⟩,after,rfl⟩
  exact List.mem_flatMap.mpr ⟨_,old,List.mem_map.mpr
    ⟨_,List.mem_flatMap.mpr ⟨_,inline,List.mem_cons_self⟩,rfl⟩⟩

theorem mixed_exact_receipt (done : Nat → Prop) :
    ∃ packet : List (GeneralDeclarativeAlternativeNeeds333.Need (restriction (support done))), Eventually (fun f => (compiled,[child]) ∈
      replay state view (finiteIndex packet) f registry interpretation root decl keep fallback targets) := by
  have planned : Planned (fun src : Index (restriction (support done)) => Eventually (fun f =>
      (compiled,[child]) ∈ replay state view src f registry interpretation root decl keep fallback targets)) := by
    apply ((endpoints_plan (independent_endpoints done)).both (exact_head done)).map
    intro src parts
    obtain ⟨limit,above⟩ := eventually_pair parts.1 parts.2
    refine ⟨limit,fun f enough => ?_⟩
    obtain ⟨guard,shapes⟩ := above f enough
    change _ ∈ replay state view src f registry interpretation root decl keep fallback targets
    unfold replay
    have observedGuard : bothEndpoints src f constructors interpretation root.arguments decl.head = true := by
      simp [bothEndpoints,guard]
    rw [ite_eq_left observedGuard]
    exact List.mem_filterMap.mpr ⟨(observed,spans),shapes,exact_body⟩
  exact planned.finite

end Yulang.GeneralDeclarativeAlternativeMixedCase333
