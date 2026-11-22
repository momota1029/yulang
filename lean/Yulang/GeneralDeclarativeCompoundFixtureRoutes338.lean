import Yulang.GeneralDeclarativeCompoundFixture338

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 1800000
namespace Yulang.GeneralDeclarativeCompoundFixtureRoutes338
open GeneralDeclarativeCompoundFixture338
open GeneralDeclarativeCompoundTree338 (Tree Forest advance)
open GeneralDeclarativeCompoundBatch338 (Ticket minted)
open GeneralDeclarativeCompoundRoutes338 (dispatch)
open GeneralDeclarativeCompoundSources338 (minted_anchors minted_valid anchored_spine)
open GeneralDeclarativeCompoundInputs338 (Inputs)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (Jobs)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeGrowth327 (fits)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)

abbrev innerArg : Capture := ⟨7,8,9⟩
abbrev outerTail : Capture := ⟨10,11,12⟩
abbrev innerField : Capture := ⟨13,14,15⟩
abbrev innerTail : Capture := ⟨16,17,18⟩
abbrev routeOuter : Entry := ⟨.field arg 7 lowPayload upPayload,innerArg⟩
abbrev routeOuterTail : Entry := ⟨.rest arg [7] lowerEnd upperEnd,outerTail⟩
abbrev jobsOuter : Jobs := [(0,routeOuter.1),(1,routeOuterTail.1)]
abbrev outLo : List (Nat × Expr) := [(7,lowPayload)]
abbrev outHi : List (Nat × Expr) := [(7,upPayload)]
theorem outerRead : Read support arg [7] outLo outHi outLo outHi lowerEnd upperEnd :=
  ⟨bounds,by decide,.inline (alias_refl _) .exactEnd loKnown,.inline (alias_refl _) .width hiKnown,rfl,rfl⟩
def outerTicket : Ticket w0.source arg [(7,inner)] :=
  ⟨outLo,outHi,outLo,outHi,lowerEnd,upperEnd,jobsOuter,outerRead,rfl⟩
abbrev w1 := advance w0 outerTicket keep
theorem outer_receipts : w1.reads = [routeOuter,routeOuterTail] := rfl
theorem projected_origin : GeneralDeclarativeCompoundSources338.Anchors
    (GeneralDeclarativeOrigins321.restriction w1.source) innerArg lowPayload upPayload :=
  minted_anchors (w := w0) (keep := keep) outerTicket (e := routeOuter) List.mem_cons_self
theorem inner_bounds : Bounds w1.state innerArg :=
  minted_valid (w := w0) (keep := keep) outerTicket (e := routeOuter) List.mem_cons_self

abbrev innerInput : List (Nat × Expr) := [(9,.variable 3)]
abbrev innerProj : Entry := ⟨.field innerArg 9 (.variable 3) (.variable 3),innerField⟩
abbrev innerResidual : Entry := ⟨.rest innerArg [9] lowerEnd upperEnd,innerTail⟩
abbrev jobsInner : Jobs := [(0,innerProj.1),(1,innerResidual.1)]
theorem innerRead : Read w1.source innerArg [9] innerInput innerInput innerInput innerInput lowerEnd upperEnd :=
  ⟨inner_bounds,by decide,anchored_spine projected_origin.1 (payloadLo _),
    anchored_spine projected_origin.2 (payloadHi _),rfl,rfl⟩
def innerTicket : Ticket w1.source innerArg [(9,.var 0)] :=
  ⟨innerInput,innerInput,innerInput,innerInput,lowerEnd,upperEnd,jobsInner,innerRead,rfl⟩
abbrev w2 := advance w1 innerTicket keep
theorem full_receipts : w2.reads = [routeOuter,routeOuterTail,innerProj,innerResidual] := rfl
theorem nested_fields : Bounds w2.state innerField :=
  minted_valid (w := w1) (keep := keep) innerTicket (e := innerProj) List.mem_cons_self
theorem nested_tail : Bounds w2.state innerTail :=
  minted_valid (w := w1) (keep := keep) innerTicket (e := innerResidual)
    (List.mem_cons_of_mem _ List.mem_cons_self)
theorem outer_tail_at_outer : Bounds w1.state outerTail :=
  minted_valid (w := w0) (keep := keep) outerTicket (e := routeOuterTail)
    (List.mem_cons_of_mem _ List.mem_cons_self)
theorem outer_tail : Bounds w2.state outerTail :=
  fits (s := w1.state) (t := w2.state)
    ((GeneralDeclarativeCompoundTree338.advance_grows (w := w1) innerTicket keep).1) outer_tail_at_outer

theorem routedInner :
    dispatch [(9,.var 0)] (minted w1.state w1.reads keep innerTicket.jobs) =
      some ([(innerProj,.var 0)],innerResidual) := rfl
theorem innerBranch : Tree keep w1 innerArg inner w2 [(0,innerField),(4,innerTail)] :=
  @Tree.record (fun _ => False) keep innerArg [(9,.var 0)] inner (.var 4)
    [(innerProj,.var 0)] innerResidual w2 [(0,innerField)] w2 [(4,innerTail)] w1 innerTicket
    (by decide) rfl routedInner
    (@Forest.cons (fun _ => False) keep w2 (innerProj,.var 0) w2 [(0,innerField)] [] w2 []
      (@Tree.binder (fun _ => False) keep innerField w2 0 nested_fields) .nil)
    (@Tree.binder (fun _ => False) keep innerTail w2 4 nested_tail)

abbrev used : List (Nat × Capture) := [(0,innerField),(4,innerTail),(1,outerTail)]
theorem routedOuter :
    dispatch [(7,inner)] (minted w0.state w0.reads keep outerTicket.jobs) =
      some ([(routeOuter,inner)],routeOuterTail) := rfl
theorem routed : Tree keep w0 arg pat w2 used :=
  @Tree.record (fun _ => False) keep arg [(7,inner)] pat (.var 1)
    [(routeOuter,inner)] routeOuterTail w2 [(0,innerField),(4,innerTail)] w2 [(1,outerTail)] w0 outerTicket
    (by decide) rfl routedOuter
    (@Forest.cons (fun _ => False) keep w1 (routeOuter,inner) w2 [(0,innerField),(4,innerTail)] [] w2 []
      innerBranch .nil)
    (@Tree.binder (fun _ => False) keep outerTail w2 1 outer_tail)

theorem observed : Inputs catalogue interpretation keep w0 root.arguments decl.head w2 used := by
  simpa only [List.append_nil] using Inputs.compound (p := pat) routed Inputs.nil

abbrev compiled := compileBody registry interpretation root decl w2.state used keep fallback targets

end Yulang.GeneralDeclarativeCompoundFixtureRoutes338
