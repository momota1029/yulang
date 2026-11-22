import Yulang.GeneralDeclarativeRepeatedWorld348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 37000
set_option maxHeartbeats 55000000
namespace Yulang.GeneralDeclarativeRepeatedChild348
open GeneralDeclarativeRepeatedPlacement348 (placedView keep requested)
open GeneralDeclarativeRepeatedLayout348 (e0 e1 e2 rows first logical intervals)
open GeneralDeclarativeRepeatedOrigins348 (support childSlice emitted_origin)
open GeneralDeclarativeRepeatedWorld348 (now rank current_rank grows leafSpans child_compile)
open GeneralDeclarativeNativeRepeatStage347 (fallback)
open GeneralDeclarativeLogicalChild343 (targets)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralLiveCompoundRegistry316 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTaggedElection340 (Election)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeStableTrace329 (Actual)
open GeneralDeclarativeGrowth327 (Extends fits)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeTrace321 (Trace)

theorem interval : Bounds placedView logical := by
  refine ⟨.interval ?_,.interval ?_⟩ <;> rw [intervals]
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem child_actual :
    Actual placedView sourceRegistry.constructors interpretation (support (reflexive placedView)) logical
      (.variant 0 (.var 0)) leafSpans := by
  refine ⟨interval,.variant 0 (.variable 0),[⟨0,.actual,2⟩],rfl,?_,?_⟩
  · exact Trace.variant (a := 2) (alias_refl _) (emitted_origin (reflexive placedView)
      (row := e1) (List.mem_cons_of_mem _ List.mem_cons_self)) .capture
  · exact .cons ⟨rfl,rfl,point_bounded _ _⟩ .nil

theorem heads :
    Inputs (support (reflexive placedView)) sourceRegistry.constructors interpretation keep placedView
      requested.arguments leaf.head placedView leafSpans [] :=
  .cons (.prior (.old (.named child_actual))) .nil

theorem choice : Election (support grows) sourceRegistry interpretation waiting requested leaf := by
  refine ⟨?_,⟨rank,current_rank⟩,fun ⟨_,_,h⟩ => h,?_,?_⟩
  · intro a seen
    change a ∈ [logical] at seen
    cases List.mem_singleton.mp seen
    exact .inl ⟨_,knows_row (emitted_origin grows (row := e0) List.mem_cons_self) rfl⟩
  · refine ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.cons (.named ?_) .nil⟩
    have range : Bounds now logical := fits grows interval
    refine ⟨range,.variant 0 (.variable 0),[⟨0,.lower,first.lower⟩],[⟨0,.upper,first.upper⟩],rfl,?_,?_⟩
    · exact Trace.variant (a := first.lower) (alias_refl _) (emitted_origin grows (row := e0) List.mem_cons_self) .capture
    · exact Trace.variant (a := first.upper) (alias_refl _) (emitted_origin grows (row := e2)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) .capture
  · intro other possible
    rcases List.mem_cons.mp possible.1.1 with prior|latest
    · rw [prior] at possible
      cases possible.1.2
    · cases List.mem_singleton.mp latest
      rfl

noncomputable def witness :
    Selected (support grows) [] sourceRegistry interpretation waiting requested leaf [] :=
  ⟨childSlice grows,keep,placedView,leafSpans,[],heads,fallback,targets,now,child_compile,
    literal (reflexive _),fun _ h => h,choice⟩

theorem rule :
    Rule (support grows) [] sourceRegistry interpretation waiting requested (.selected leaf.id []) :=
  .whole witness

end Yulang.GeneralDeclarativeRepeatedChild348
