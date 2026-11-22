import Yulang.GeneralDeclarativeNestedReplay332
import Yulang.GeneralDeclarativeNestedSiblingsModels332
import Yulang.GeneralDeclarativeNestedRepeat332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativeNestedReplayCases332
open GeneralDeclarativeNestedReplay332 (replay)
open GeneralDeclarativeNestedHeadList332 (captureArgs capture_sound)
open GeneralDeclarativeNestedSiblingsFrame332 (indexed source keep targets actual_head parent childList origins stage)
open GeneralDeclarativeNestedSiblingsDecl332 (registry impl)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedExample332 (interpretation pat)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeNestedFrame332 (fallback spans)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarationExamples (constructors)

theorem actual_replay (done : Nat → Prop) :
    replay registry interpretation root impl (indexed done) source keep fallback targets =
      some (parent,childList) := rfl

theorem rejects_wrong_arity (done : Nat → Prop) :
    captureArgs (indexed done) constructors interpretation keep source [point 0] [pat,.var 0] = none := rfl

abbrev second := appendFacts stage [⟨11,.variable 11⟩]
abbrev twoSpans : List (Nat × Capture) := spans ++ [(0,point 11)]

/-- Across distinct actual head arguments, a second occurrence is not
filtered out or duplicated by allocation. The later tie relates two
different original names, not two copies of the first center. -/
theorem across_arguments (done : Nat → Prop) :
    captureArgs (indexed done) constructors interpretation keep source [point 0,point 11] [pat,.var 0] =
      some (second,twoSpans) := rfl

theorem cross_argument_tie :
    (tieState second twoSpans fallback).equations = second.equations ++ [⟨3,.variable 11⟩] := rfl

open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open CommonNominalFullCarrier (common_union_is_join subtype_refl)
open GeneralDeclarativeNestedModels328 (payload_gt_int)

theorem cross_argument_conflict (done : Nat → Prop) :
    (∃ m, Models source m) ∧ ¬∃ m, Models (tieState second twoSpans fallback) m := by
  refine ⟨⟨_,GeneralDeclarativeNestedSiblingsModels332.original⟩,?_⟩
  rintro ⟨m,after⟩
  have extend := (capture_sound (indexed done) (GeneralDeclarativeClauseBatch327.reflexive source)
    (fun a h => by
      rcases List.mem_cons.mp h with rfl|rest
      · exact point_bounded _ _
      · cases List.mem_singleton.mp rest
        exact point_bounded _ _)
    (across_arguments done)).1.grows
  obtain ⟨before,emitted⟩ := (model_append (s := second) (rows := [⟨3,.variable 11⟩]) m).mp after
  have fits := restrict extend m before
  have scalar := fits.2 GeneralDeclarativeNestedExample332.scalar (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have boolean := fits.2 GeneralDeclarativeNestedSiblingsFrame332.scalar11 (List.mem_append_right _ List.mem_cons_self)
  have tied := emitted ⟨3,.variable 11⟩ List.mem_cons_self
  have nope := (eqv_trans (eqv_symm boolean) (eqv_trans (eqv_symm tied) scalar)).1
  exact payload_gt_int ((common_union_is_join ..).mpr ⟨subtype_refl _,nope⟩)

end Yulang.GeneralDeclarativeNestedReplayCases332
