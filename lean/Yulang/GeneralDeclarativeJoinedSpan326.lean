import Yulang.GeneralDeclarativePairUnion326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeJoinedSpan326
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativePairNames326 (Span Defines generated appended first second projection keepNames)
open GeneralDeclarativePairSpan326 (state left_bound)
open GeneralDeclarativePairUnion326 (Coordinates center_rule)
open GeneralDeclarativeWhereIntervals325 (withInterval unchanged called_bounds)
open GeneralDeclarativeEqualities322 (Derives entails semantic)
open GeneralDeclarativeEntailment320 (Entails model_append)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype Equivalent common_pair_iff subtype_trans)

def eval (m : Assignment) (e : Expr) := value (environment m) .actual e
def Fits (m : Assignment) (span : Span) := Subtype (eval m span.low) (eval m span.actual) ∧
  Subtype (eval m span.actual) (eval m span.high)

theorem actual_intervals {s : State} {arg : Capture} {l r : Span}
    (bounds : Bounds s arg)
    (lower : Derives s (.variable arg.lower) (pair l.low r.low))
    (observed : Derives s (.variable arg.center) e)
    (projected : Coordinates e l.actual r.actual)
    (upper : Derives s (.variable arg.upper) (pair l.high r.high))
    (m : Assignment) (valid : Models s m) : Fits m l ∧ Fits m r := by
  have range := bounds_sound bounds m valid
  have lo := entails lower m valid
  have actual := center_rule observed projected m valid
  have hi := entails upper m valid
  have toward := (common_pair_iff (eval m l.low) (eval m r.low) (eval m l.actual) (eval m r.actual)).mp
    (subtype_trans lo.2 (subtype_trans range.1 actual.1))
  have away := (common_pair_iff (eval m l.actual) (eval m r.actual) (eval m l.high) (eval m r.high)).mp
    (subtype_trans actual.2 (subtype_trans range.2 hi.1))
  exact ⟨⟨toward.1,away.1⟩,⟨toward.2,away.2⟩⟩

theorem named_fit {s : State} {cap : Capture} (stored : Defines s cap values)
    (m : Assignment) (fit : Models s m) (valid : Fits m values) :
    Subtype (m cap.lower).1 (m cap.center).1 ∧ Subtype (m cap.center).1 (m cap.upper).1 := by
  have lower := semantic stored.1 m fit
  have actual := semantic stored.2.1 m fit
  have upper := semantic stored.2.2 m fit
  exact ⟨subtype_trans lower.1 (subtype_trans valid.1 actual.2),
    subtype_trans actual.1 (subtype_trans valid.2 upper.2)⟩

theorem defined_model {s : State} {arg : Capture} {l r : Span}
    (bounds : Bounds s arg) (low : Derives s (.variable arg.lower) (pair l.low r.low))
    (shown : Derives s (.variable arg.center) e) (walk : Coordinates e l.actual r.actual)
    (high : Derives s (.variable arg.upper) (pair l.high r.high))
    (keep : List Nat) (m : Assignment) :
    Models (state s keep l r) m ↔ Models (appended s keep l r) m := by
  let t := appended s keep l r
  have ranges (valid : Models t m) := actual_intervals bounds low shown walk high m ((model_append m).mp valid).1
  have left := unchanged (s := t) (arg := first s keep l r) m
    (fun valid => named_fit (generated s keep l r).1 m valid (ranges valid).1)
  have right := unchanged (s := withInterval t (first s keep l r)) (arg := second s keep l r) m (fun valid => by
    have existsHere := left.mp valid
    exact named_fit (generated s keep l r).2 m existsHere (ranges existsHere).2)
  exact right.trans left

/-- A raw ordinary center that is a join of visible products still
yields its two canonical new intervals conservatively. Both the
projections and the result keep the actual join, not an endpoint. -/
theorem named_join {s : State} {arg : Capture} {l r : Span}
    (bounds : Bounds s arg) (low : Derives s (.variable arg.lower) (pair l.low r.low))
    (shown : Derives s (.variable arg.center) e) (walk : Coordinates e l.actual r.actual)
    (high : Derives s (.variable arg.upper) (pair l.high r.high))
    (keep : List Nat) (m : Assignment) :
    Bounds (state s keep l r) (first s keep l r) ∧ Bounds (state s keep l r) (second s keep l r) ∧
    (Models s m ↔ ∃ next, Models (state s keep l r) next ∧
      ∀ n ∈ stateNames s ++ keepNames s keep l r, next n = m n) :=
  ⟨left_bound _ _ _ _,called_bounds _ _,(projection s keep l r m).trans
    (exists_congr (fun next => and_congr_left' (defined_model bounds low shown walk high keep next).symm))⟩

theorem named_actual {s : State} {arg : Capture} {l r : Span}
    (bounds : Bounds s arg) (low : Derives s (.variable arg.lower) (pair l.low r.low))
    (shown : Derives s (.variable arg.center) e) (walk : Coordinates e l.actual r.actual)
    (high : Derives s (.variable arg.upper) (pair l.high r.high)) (keep : List Nat) :
    Entails (state s keep l r) ⟨arg.center,pair (.variable (first s keep l r).center)
      (.variable (second s keep l r).center)⟩ := by
  intro m valid
  have base := (defined_model bounds low shown walk high keep m).mp valid
  have pulled := ((model_append m).mp base).1
  have seen := center_rule shown walk m pulled
  have a := semantic (generated s keep l r).1.2.1 m base
  have b := semantic (generated s keep l r).2.2.1 m base
  exact eqv_trans seen ⟨(common_pair_iff ..).mpr ⟨a.2,b.2⟩,(common_pair_iff ..).mpr ⟨a.1,b.1⟩⟩

end Yulang.GeneralDeclarativeJoinedSpan326
