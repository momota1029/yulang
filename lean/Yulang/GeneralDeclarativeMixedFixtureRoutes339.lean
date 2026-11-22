import Yulang.GeneralDeclarativeMixedFixtureBase339

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 1800000
namespace Yulang.GeneralDeclarativeMixedFixtureRoutes339
open GeneralDeclarativeMixedFixtureBase339
open GeneralDeclarativeCompoundTree338 (World advance)
open GeneralDeclarativeMixedTree339 (Node Forest exact_tree)
open GeneralDeclarativeCompoundInputs338 (oldAfter)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeCompoundBatch338 (Ticket minted)
open GeneralDeclarativeCompoundRoutes338 (dispatch)
open GeneralDeclarativeCompoundSources338 (minted_anchors minted_valid anchored_spine)
open GeneralDeclarativeMixedInputs339 (Inputs)
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

abbrev innerInput : List (Nat × Expr) := [(9,payload)]
abbrev innerProj : Entry := ⟨.field innerArg 9 payload payload,innerField⟩
abbrev innerResidual : Entry := ⟨.rest innerArg [9] lowerEnd upperEnd,innerTail⟩
abbrev jobsInner : Jobs := [(0,innerProj.1),(1,innerResidual.1)]
theorem innerRead : Read w1.source innerArg [9] innerInput innerInput innerInput innerInput lowerEnd upperEnd :=
  ⟨inner_bounds,by decide,anchored_spine projected_origin.1 (payloadLo _),
    anchored_spine projected_origin.2 (payloadHi _),rfl,rfl⟩
def innerTicket : Ticket w1.source innerArg [(9,.variant 8 (.var 0))] :=
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

abbrev leafPat : GeneralDeclarationPatterns.Pattern := .variant 8 (.var 0)
abbrev plan : GeneralDeclarativeArityPlan330.Plan := .tagged 8 3 3 (.capture 0)
abbrev run := GeneralDeclarativeArityRun330.run (names w2.reads ++ keep) w2.state innerField plan
abbrev payloadArg : Capture := ⟨3,19,3⟩
theorem payload_bind : run.binds = [(0,payloadArg)] := rfl

theorem projectedReads : GeneralDeclarativeArityPlan330.Reads
    (GeneralDeclarativeOrigins321.restriction w2.source) 13 15 plan :=
  .tagged
    (.row (GeneralDeclarativeCompoundBatch338.authored_row (old := w1.reads) (keep := keep)
      innerTicket (e := innerProj) List.mem_cons_self (GeneralDeclarativeCompoundReadback338.stored_low innerProj)))
    (.row (GeneralDeclarativeCompoundBatch338.authored_row (old := w1.reads) (keep := keep)
      innerTicket (e := innerProj) List.mem_cons_self (GeneralDeclarativeCompoundReadback338.stored_high innerProj)))
    .capture

theorem sourceLeaf : GeneralDeclarativeWitnessHead334.Argument w2.source catalogue interpretation
    (names w2.reads ++ keep) w2.state innerField leafPat run.state run.binds :=
  .projected nested_fields rfl projectedReads

abbrev w3 := oldAfter sourceLeaf

theorem leafActual : Node catalogue interpretation keep w2 innerField leafPat w3 [(0,payloadArg)] :=
  Node.projected sourceLeaf

theorem untilLeaf : w2.Grows w3 := (GeneralDeclarativeCompoundInputs338.old_sound sourceLeaf).1

theorem finishTail : Bounds w3.state innerTail := fits untilLeaf.1 nested_tail
theorem finishOuter : Bounds w3.state outerTail := fits untilLeaf.1 outer_tail

theorem routedInner :
    dispatch [(9,leafPat)] (minted w1.state w1.reads keep innerTicket.jobs) =
      some ([(innerProj,leafPat)],innerResidual) := rfl
theorem innerBranch : Node catalogue interpretation keep w1 innerArg inner w3 [(0,payloadArg),(4,innerTail)] :=
  @Node.record (fun _ => False) catalogue interpretation keep innerArg [(9,leafPat)] inner (.var 4)
    [(innerProj,leafPat)] innerResidual w3 [(0,payloadArg)] w3 [(4,innerTail)] w1 innerTicket
    (by decide) rfl routedInner
    (@Forest.cons (fun _ => False) catalogue interpretation keep w2 (innerProj,leafPat) w3 [(0,payloadArg)] [] w3 []
      leafActual .nil)
    (@Node.binder (fun _ => False) catalogue interpretation keep innerTail w3 4 finishTail)

abbrev used : List (Nat × Capture) := [(0,payloadArg),(4,innerTail),(1,outerTail)]
theorem routedOuter :
    dispatch [(7,inner)] (minted w0.state w0.reads keep outerTicket.jobs) =
      some ([(routeOuter,inner)],routeOuterTail) := rfl
theorem routed : Node catalogue interpretation keep w0 arg pat w3 used :=
  @Node.record (fun _ => False) catalogue interpretation keep arg [(7,inner)] pat (.var 1)
    [(routeOuter,inner)] routeOuterTail w3 [(0,payloadArg),(4,innerTail)] w3 [(1,outerTail)] w0 outerTicket
    (by decide) rfl routedOuter
    (@Forest.cons (fun _ => False) catalogue interpretation keep w1 (routeOuter,inner) w3 [(0,payloadArg),(4,innerTail)] [] w3 []
      innerBranch .nil)
    (@Node.binder (fun _ => False) catalogue interpretation keep outerTail w3 1 finishOuter)

theorem observed : Inputs catalogue interpretation keep w0 root.arguments decl.head w3 used := by
  simpa only [List.append_nil] using Inputs.cons (p := pat) routed Inputs.nil

abbrev compiled := compileBody registry interpretation root decl w3.state used keep fallback targets

end Yulang.GeneralDeclarativeMixedFixtureRoutes339
