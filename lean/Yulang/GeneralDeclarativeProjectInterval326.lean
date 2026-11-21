import Yulang.GeneralDeclarativeProjectPair326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectInterval326
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativePairNames326 (Span appended generated first second projection keepNames)
open GeneralDeclarativePairSpan326 (state left_bound)
open GeneralDeclarativeJoinedSpan326 (Fits eval named_fit)
open GeneralDeclarativeProjectPair326 (project recorded)
open GeneralDeclarativePairUnion326 (center_rule)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeWhereIntervals325 (withInterval unchanged called_bounds)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeEntailment320 (Entails model_append)
open GeneralDeclarativePairCenters326 (pair)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonNominalFullCarrier (common_pair_iff subtype_trans)

/-- Compute two actual logical intervals from three independently read
finite visible pair expressions. No projection substitutes a lower or
upper expression for the center. Each expression can itself contain a
finite join of visible pairs. -/
def projectAll (low mid high : Expr) : Option (Span × Span) := do
  let (ll,lr) ← project low
  let (ml,mr) ← project mid
  let (hl,hr) ← project high
  pure (⟨ll,ml,hl⟩,⟨lr,mr,hr⟩)

theorem pieces (read : projectAll low mid high = some (l,r)) :
    project low = some (l.low,r.low) ∧ project mid = some (l.actual,r.actual) ∧
      project high = some (l.high,r.high) := by
  cases lo : project low with
  | none => simp [projectAll,lo] at read
  | some a =>
    rcases a with ⟨ll,lr⟩
    cases center : project mid with
    | none => simp [projectAll,lo,center] at read
    | some b =>
      rcases b with ⟨ml,mr⟩
      cases hi : project high with
      | none => simp [projectAll,lo,center,hi] at read
      | some c =>
        rcases c with ⟨hl,hr⟩
        have matchRead : ((⟨ll,ml,hl⟩,⟨lr,mr,hr⟩) : Span × Span) = (l,r) := by
          simpa [projectAll,lo,center,hi] using read
        cases matchRead
        exact ⟨rfl,rfl,rfl⟩

theorem all_fits {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lowSeen : Derives s (.variable arg.lower) low)
    (midSeen : Derives s (.variable arg.center) mid) (highSeen : Derives s (.variable arg.upper) high)
    (read : projectAll low mid high = some (l,r)) (m) (valid : Models s m) :
    Fits m l ∧ Fits m r := by
  obtain ⟨lowRead,midRead,highRead⟩ := pieces read
  have lo := center_rule lowSeen (recorded lowRead) m valid
  have center := center_rule midSeen (recorded midRead) m valid
  have hi := center_rule highSeen (recorded highRead) m valid
  have bound := bounds_sound bounds m valid
  have toward := (common_pair_iff (eval m l.low) (eval m r.low) (eval m l.actual) (eval m r.actual)).mp
    (subtype_trans lo.2 (subtype_trans bound.1 center.1))
  have away := (common_pair_iff (eval m l.actual) (eval m r.actual) (eval m l.high) (eval m r.high)).mp
    (subtype_trans center.2 (subtype_trans bound.2 hi.1))
  exact ⟨⟨toward.1,away.1⟩,⟨toward.2,away.2⟩⟩

theorem unchanged_models {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lowSeen : Derives s (.variable arg.lower) low)
    (midSeen : Derives s (.variable arg.center) mid) (highSeen : Derives s (.variable arg.upper) high)
    (read : projectAll low mid high = some (l,r)) (kept : List Nat) (m) :
    Models (state s kept l r) m ↔ Models (appended s kept l r) m := by
  let t := appended s kept l r
  have fits (valid : Models t m) := all_fits bounds lowSeen midSeen highSeen read m ((model_append m).mp valid).1
  have left := unchanged (s := t) (arg := first s kept l r) m
    (fun valid => named_fit (generated s kept l r).1 m valid (fits valid).1)
  have right := unchanged (s := withInterval t (first s kept l r)) (arg := second s kept l r) m (fun valid => by
    have previous := left.mp valid
    exact named_fit (generated s kept l r).2 m previous (fits previous).2)
  exact right.trans left

theorem names_and_actual {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lowSeen : Derives s (.variable arg.lower) low)
    (midSeen : Derives s (.variable arg.center) mid) (highSeen : Derives s (.variable arg.upper) high)
    (read : projectAll low mid high = some (l,r)) (kept : List Nat) :
    Bounds (state s kept l r) (first s kept l r) ∧ Bounds (state s kept l r) (second s kept l r) ∧
    (∀ m, Models s m ↔ ∃ next, Models (state s kept l r) next ∧
      ∀ n ∈ stateNames s ++ keepNames s kept l r, next n = m n) ∧
    Entails (state s kept l r) ⟨arg.center,pair (.variable (first s kept l r).center)
      (.variable (second s kept l r).center)⟩ := by
  have unchangedAt := unchanged_models bounds lowSeen midSeen highSeen read kept
  refine ⟨left_bound _ _ _ _,called_bounds _ _,fun m => (projection s kept l r m).trans
    (exists_congr fun next => and_congr_left' (unchangedAt next).symm),?_⟩
  intro m valid
  have base := (unchangedAt m).mp valid
  have pulled := ((model_append m).mp base).1
  have seen := center_rule midSeen (recorded (pieces read).2.1) m pulled
  have a := semantic (generated s kept l r).1.2.1 m base
  have b := semantic (generated s kept l r).2.2.1 m base
  exact eqv_trans seen ⟨(common_pair_iff ..).mpr ⟨a.2,b.2⟩,(common_pair_iff ..).mpr ⟨a.1,b.1⟩⟩

end Yulang.GeneralDeclarativeProjectInterval326
