import Yulang.GeneralDeclarativeBridgeInstance343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16500
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeReceiptSplit343
open GeneralDeclarativeWithheldInput343 (withheld)
open GeneralDeclarativeCurrentWorld343 (now grows rank current_rank leafSpans child_compile)
open GeneralDeclarativeCurrentOrigins343 (done completed ChildReceipt recorded)
open GeneralDeclarativeFrameShape343 (e0 e1 e2 childRows b0 output_ordinary)
open GeneralDeclarativePlacement343 (view symbolic)
open GeneralDeclarativeCurrentChild343 (interval)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeLogicalChild343 (child fallback targets)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand)
open GeneralDeclarativeOrigins321 (Supported restriction from_completed backed_iff)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeGrowth327 (fits)
open GeneralDeclarativeStableTrace329 (Actual)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeTaggedElection340 (Election)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeTrace321 (Trace)
open GeneralWhereOriginSingleSource318 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation root)
open GeneralLiveCompoundRegistry316 (leaf)

noncomputable def localSupport : Supported view done :=
  ⟨fun row origin => ChildReceipt row ∧ origin = .output root.identity,
    fun h => output_ordinary _ h.1.printed⟩

theorem present {row : Equation} (listed : row ∈ childRows) : row ∈ (restriction localSupport).equations :=
  from_completed _ ⟨recorded listed,rfl⟩ completed

theorem present_current {row : Equation} (listed : row ∈ childRows) : row ∈ (restriction withheld).equations :=
  from_completed _ ⟨recorded listed,rfl⟩ completed

noncomputable def slice : Slice withheld :=
  ⟨view,localSupport,grows,⟨grows.constraints,grows.intervals,fun row known => by
    obtain ⟨_,came,_⟩ := (backed_iff localSupport row).mp known
    exact present_current came.1.printed⟩⟩

theorem observed :
    Actual view sourceRegistry.constructors interpretation localSupport symbolic
      (.variant 0 (.var 0)) leafSpans := by
  refine ⟨interval,.variant 0 (.variable 0),[⟨0,.actual,2⟩],rfl,?_,?_⟩
  · exact Trace.variant (a := 2) (alias_refl _) (present (row := e1)
      (List.mem_cons_of_mem _ List.mem_cons_self)) .capture
  · exact .cons ⟨rfl,rfl,point_bounded _ _⟩ .nil

theorem heads : Inputs localSupport sourceRegistry.constructors interpretation kept view
    (child kept).arguments leaf.head view leafSpans [] :=
  .cons (.prior (.old (.named observed))) .nil

theorem choice : Election withheld sourceRegistry interpretation waiting (child kept) leaf := by
  refine ⟨?_,⟨rank,current_rank⟩,fun ⟨_,_,unreached⟩ => unreached,?_,?_⟩
  · intro arg there
    change arg ∈ [symbolic] at there
    cases List.mem_singleton.mp there
    exact .inl ⟨_,knows_row (present_current (row := e0) List.mem_cons_self) rfl⟩
  · refine ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.cons (.named ?_) .nil⟩
    have range : Bounds now symbolic := fits grows interval
    refine ⟨range,.variant 0 (.variable 0),[⟨0,.lower,b0.lower⟩],[⟨0,.upper,b0.upper⟩],rfl,?_,?_⟩
    · exact Trace.variant (a := b0.lower) (alias_refl _) (present_current (row := e0) List.mem_cons_self) .capture
    · exact Trace.variant (a := b0.upper) (alias_refl _) (present_current (row := e2)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) .capture
  · intro other candidate
    rcases List.mem_cons.mp candidate.1.1 with prior|latest
    · rw [prior] at candidate
      cases candidate.1.2
    · cases List.mem_singleton.mp latest
      rfl

noncomputable def witness :
    Selected withheld [] sourceRegistry interpretation waiting (child kept) leaf [] :=
  ⟨slice,kept,view,leafSpans,[],heads,fallback,targets,now,child_compile,literal (reflexive _),fun _ h => h,choice⟩

/-- With authored input withheld but completion authority retained,
the genuine emitted child still has its exact local witness; the
root cannot obtain one from that receipt. This is the converse
independence control, not an actual additional solver run. -/
theorem independent :
    Rule withheld [] sourceRegistry interpretation waiting (child kept) (.selected leaf.id []) ∧
    ∀ key children, ¬ Rule withheld [] sourceRegistry interpretation waiting actualDemand (.selected key children) :=
  ⟨.whole witness,GeneralDeclarativeWithheldInput343.no_authored_no_root⟩

end Yulang.GeneralDeclarativeReceiptSplit343
