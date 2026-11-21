import Yulang.GeneralDeclarativePairNames326
import Yulang.GeneralDeclarativeWhereIntervals325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePairSpan326
open GeneralDeclarativeHead320 (State Models Equation environment)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativePairCenters326 (pair coordinate_ranges)
open GeneralDeclarativePairNames326 (Span appended first second Defines generated projection keepNames)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeWhereIntervals325 (withInterval called_bounds unchanged)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeInequality322 (Le sound)
open GeneralDeclarativeEntailment320 (model_append Entails)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype Equivalent subtype_trans common_pair_iff)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

def Ranges (s : State) (span : Span) : Prop :=
  Le s span.low span.actual ∧ Le s span.actual span.high

def state (s : State) (keep : List Nat) (l r : Span) : State :=
  withInterval (withInterval (appended s keep l r) (first s keep l r)) (second s keep l r)

theorem left_bound (s : State) (keep : List Nat) (l r : Span) :
    Bounds (state s keep l r) (first s keep l r) := by
  exact ⟨.interval (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)),
    .interval (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem named_range {s t : State} {cap : Capture} {terms : Span}
    (within : Ranges s terms) (existsHere : Defines t cap terms)
    (m : Assignment) (old : Models s m) (present : Models t m) :
    Subtype (m cap.lower).1 (m cap.center).1 ∧ Subtype (m cap.center).1 (m cap.upper).1 := by
  have lo := semantic existsHere.1 m present
  have mid := semantic existsHere.2.1 m present
  have hi := semantic existsHere.2.2 m present
  exact ⟨subtype_trans lo.1 (subtype_trans (sound within.1 m old) mid.2),
    subtype_trans mid.1 (subtype_trans (sound within.2 m old) hi.2)⟩

theorem the_same_models {s : State} {l r : Span}
    (ranges : Ranges s l ∧ Ranges s r) (keep : List Nat) (m : Assignment) :
    Models (state s keep l r) m ↔ Models (appended s keep l r) m := by
  let a := appended s keep l r
  have firstRange : Models a m → _ := fun current =>
    named_range (cap := first s keep l r) ranges.1 (generated s keep l r).1 m ((model_append _).mp current).1 current
  have left := unchanged m firstRange
  have right := unchanged (s := withInterval a (first s keep l r)) (arg := second s keep l r) m (fun afterOne => by
    have current := left.mp afterOne
    exact named_range ranges.2 (generated s keep l r).2 m ((model_append _).mp current).1 current)
  exact right.trans left

/-- Independently observed lower, center and upper pair equations give
two logical interval triples in a definitionally conservative state
extension. Source and fixed output names are preserved in both directions. -/
theorem both_named {s : State} {root : Capture} {l r : Span}
    (bounds : Bounds s root) (lo : Derives s (.variable root.lower) (pair l.low r.low))
    (mid : Derives s (.variable root.center) (pair l.actual r.actual))
    (hi : Derives s (.variable root.upper) (pair l.high r.high))
    (keep : List Nat) (m : Assignment) :
    Bounds (state s keep l r) (first s keep l r) ∧ Bounds (state s keep l r) (second s keep l r) ∧
    (Models s m ↔ ∃ next, Models (state s keep l r) next ∧
        ∀ n ∈ stateNames s ++ keepNames s keep l r, next n = m n) := by
  have both : Ranges s l ∧ Ranges s r := coordinate_ranges bounds lo mid hi
  exact ⟨left_bound _ _ _ _,called_bounds _ _,(projection s keep l r m).trans
    (exists_congr (fun next => and_congr_left' (the_same_models both keep next).symm))⟩

theorem projected_center {s : State} {root : Capture} {l r : Span}
    (bounds : Bounds s root) (lo : Derives s (.variable root.lower) (pair l.low r.low))
    (mid : Derives s (.variable root.center) (pair l.actual r.actual))
    (hi : Derives s (.variable root.upper) (pair l.high r.high)) (keep : List Nat) :
    Entails (state s keep l r) ⟨root.center,pair (.variable (first s keep l r).center)
      (.variable (second s keep l r).center)⟩ := by
  intro m here
  have both : Ranges s l ∧ Ranges s r := coordinate_ranges bounds lo mid hi
  have newModel := (the_same_models both keep m).mp here
  have oldModel := ((model_append m).mp newModel).1
  have lhs := semantic mid m oldModel
  have f := semantic (generated s keep l r).1.2.1 m newModel
  have g := semantic (generated s keep l r).2.2.1 m newModel
  exact eqv_trans lhs ⟨(common_pair_iff ..).mpr ⟨f.2,g.2⟩,(common_pair_iff ..).mpr ⟨f.1,g.1⟩⟩

end Yulang.GeneralDeclarativePairSpan326
