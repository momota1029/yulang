import Yulang.GeneralDeclarativePairSpan326
import Yulang.GeneralDeclarativeForwardHead325
import Yulang.GeneralDeclarativeOrdinaryIncrease325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePairProbe326
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeEqualities322 (Derives entails Forest)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeTraceExpand323 (convert expands)
open GeneralDeclarativeTraceTransfer325 (ordinary)
open GeneralDeclarativeTermWalk322 (Walk Binds split_binds)
open GeneralDeclarativePairCenters326 (pair project_first project_second)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeForwardHead325 (by_walk)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)

/-- The supported endpoint walk names the two *lower observations*,
not the two actual components. Their authorization is retained. -/
theorem components {s : State}
    (seen : Trace s mode n (pair p q) raw) :
    ∃ first second one two,
      Derives s (.variable n) (pair (.variable first) (.variable second)) ∧
      Trace s mode first p one ∧ Trace s mode second q two ∧ raw = one ++ two := by
  unfold pair at seen
  cases seen with
  | primitive equal stored walk =>
    cases walk with
    | cons firstWalk rests =>
      cases rests with
      | cons lastWalk endWalk =>
        cases endWalk
        exact ⟨_,_,_,_,.trans (.congruent (.variable equal)) (.row stored),firstWalk,lastWalk,
          by simp⟩

theorem authorized_lower {s : State} {support : Supported s complete}
    (seen : Trace (restriction support) .lower n (pair p q) raw) :
    ∃ first second one two,
      Derives s (.variable n) (pair (.variable first) (.variable second)) ∧
      Trace (restriction support) .lower first p one ∧
      Trace (restriction support) .lower second q two ∧ raw = one ++ two := by
  obtain ⟨left,right,one,two,known,h,k,exact⟩ := components seen
  -- Use the same head and the same two names by carrying the derivation,
  -- not by choosing a second traversal.
  have advance : GeneralDeclarativeOrdinaryIncrease325.Extends (restriction support) s := by
    refine ⟨rfl,?_⟩
    intro row present
    obtain ⟨origin,recorded,_⟩ := (GeneralDeclarativeOrigins321.backed_iff support row).mp present
    exact support.ordinary recorded
  exact ⟨left,right,one,two,GeneralDeclarativeOrdinaryIncrease325.derives advance known,h,k,exact⟩

/-- Independent real center plus the two normalized coordinate walks
produce the head batch without a literal equation at the center.
Binding is checked at actual names, rather than at the lower witnesses. -/
theorem normalized_center {s : State}
    (printed : translate c i (normalize p) = some (pair leftCode rightCode))
    (actual : Derives s (.variable arg.center) (pair left right))
    (first : Walk .actual left leftCode one) (second : Walk .actual right rightCode two)
    (sharing : Binds s cap (one ++ two)) :
    Result s (fact c i cap arg p) := by
  apply by_walk printed (entails actual) ?_ sharing
  simpa only [List.append_nil,pair] using Walk.primitive (.cons first (.cons second .nil))

end Yulang.GeneralDeclarativePairProbe326
