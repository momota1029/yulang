import Yulang.GeneralDeclarativeRepeatedProjection327
import Yulang.GeneralDeclarativeGrowth327
import Yulang.GeneralDeclarativeForwardHead325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatedHead327
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativePairNames326 (Span appended generated first second keepNames terms)
open GeneralDeclarativePairSpan326 (state)
open GeneralDeclarativeProjectInterval326 (projectAll names_and_actual unchanged_models pieces)
open GeneralDeclarativeRepeatedProjection327 (mergeState merged link_from_observations)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeGrowth327 (Extends trans ordinary span facts fits aliases derives restrict)
open GeneralDeclarativeEqualities322 (Derives entails semantic)
open GeneralDeclarativeMergeCenters324 (align links_recorded)
open GeneralDeclarativeAggregate324 (aligned ready now_bounds kept)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeTermWalk322 (Walk Binds)
open GeneralDeclarativeNFHead324 (fact)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeNewNames321 (supply)

theorem projection_grows (s : State) (protect : List Nat) (l r : Span) :
    Extends (appended s protect l r) (state s protect l r) :=
  trans (span _ _) (span _ _)

theorem aggregate_grows (s : State) (protect : List Nat) (l r : Span) :
    Extends (state s protect l r) (mergeState s protect l r) :=
  trans (ordinary _ _) (trans (ordinary _ _) (ordinary _ _))

theorem original_grows (s : State) (protect : List Nat) (l r : Span) :
    Extends s (mergeState s protect l r) :=
  trans (facts _ _) (trans (projection_grows s protect l r) (aggregate_grows s protect l r))

theorem same_current {s : State} (protect : List Nat) (l r : Span) :
    Derives (mergeState s protect l r) (.variable (second s protect l r).center)
      (.variable (merged s protect l r).center) := by
  let projected := state s protect l r
  let firstSpan := first s protect l r
  let lastSpan := second s protect l r
  let inner := aligned projected firstSpan [lastSpan]
  have other : lastSpan ∈ firstSpan :: [lastSpan] := List.mem_cons_of_mem _ List.mem_cons_self
  have equal := links_recorded (s := projected) other
  exact derives (trans (ordinary inner _) (ordinary _ _)) (.congruent (.variable (.bounds equal.1 equal.2)))

/-- The approved shared-span operation reads the new center twice in
the regular head batch. This is a theorem on any pair/join visible
expression, even when the original center had no literal pair row. -/
theorem actual_head {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lo : Derives s (.variable arg.lower) low)
    (mid : Derives s (.variable arg.center) midCode) (hi : Derives s (.variable arg.upper) high)
    (read : projectAll low midCode high = some (l,r)) (protect : List Nat) :
    Entails (mergeState s protect l r) ⟨arg.center,pair (.variable (merged s protect l r).center)
      (.variable (merged s protect l r).center)⟩ := by
  intro m valid
  have named := (names_and_actual bounds lo mid hi read protect).2.2.2 m
    (restrict (aggregate_grows s protect l r) m valid)
  have repeated : Derives (mergeState s protect l r)
      (pair (.variable (first s protect l r).center) (.variable (second s protect l r).center))
      (pair (.variable (merged s protect l r).center) (.variable (merged s protect l r).center)) :=
    .primitive (.cons (.refl _) (.cons (same_current protect l r) .nil))
  exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans named (semantic repeated m valid)

theorem compiled_head {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lo : Derives s (.variable arg.lower) low)
    (mid : Derives s (.variable arg.center) midCode) (hi : Derives s (.variable arg.upper) high)
    (read : projectAll low midCode high = some (l,r)) (protect : List Nat)
    (sourceCode : translate c i (normalize p) = some (pair (.variable binder) (.variable binder)))
    (exactCapture : cap binder = merged s protect l r) :
    Result (mergeState s protect l r) (fact c i cap arg p) := by
  apply GeneralDeclarativeForwardHead325.by_walk sourceCode (actual_head bounds lo mid hi read protect)
    (Walk.primitive (.cons .capture (.cons .capture .nil)))
  intro o found
  change o ∈ [_,_] at found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl|rfl <;> rw [GeneralDeclarativeHead320.byMode,exactCapture] <;> exact .refl _

end Yulang.GeneralDeclarativeRepeatedHead327
