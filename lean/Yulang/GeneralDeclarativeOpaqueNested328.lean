import Yulang.GeneralDeclarativeOpaquePlan328
import Yulang.GeneralDeclarativeOpaqueNominal328

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
namespace Yulang.GeneralDeclarativeOpaqueNested328
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaquePlan328 (Plan Read grows)
open GeneralDeclarativeOpaqueConserve328 (Retains chain pairs variants refl)
open GeneralDeclarativeOpaqueIntervals328 (Ends left right ready)
open GeneralDeclarativeGrowth327 (Extends derives fits)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativePairCenters326 (pair)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)

structure Named where
  state : State
  form : Expr
  binds : List (Nat × Capture)

def run (keep : List Nat) (s : State) (arg : Capture) : Plan → Named
  | .capture b => ⟨s,.variable arg.center,[(b,arg)]⟩
  | .product e a b =>
    let t := ready s arg.center keep e
    let x := run keep t (left s arg.center keep e) a
    let y := run keep x.state (right s arg.center keep e) b
    ⟨y.state,pair x.form y.form,x.binds ++ y.binds⟩
  | .tagged tag lo hi plan =>
    let t := GeneralDeclarativeOpaqueVariantNames328.ready s tag arg.center lo hi keep
    let x := run keep t (GeneralDeclarativeOpaqueVariantNames328.names s arg.center lo hi keep) plan
    ⟨x.state,.variant tag x.form,x.binds⟩
  | .invariant tag lo _ plan =>
    let t := GeneralDeclarativeOpaqueNominal328.ready s arg.center tag lo
    let x := run keep t (GeneralDeclarativeOpaqueNominal328.point lo) plan
    ⟨x.state,.nominal tag [x.form],x.binds⟩

def occurrences (binds : List (Nat × Capture)) : List Occurrence :=
  binds.map fun (key,arg) => ⟨key,.actual,.variable arg.center⟩

structure Builds (s : State) (keep : List Nat) (arg : Capture) (plan : Plan) : Prop where
  modeled : Retains s (run keep s arg plan).state keep
  center : Derives (run keep s arg plan).state (.variable arg.center) (run keep s arg plan).form
  ordered : Walk .actual (run keep s arg plan).form plan.code (occurrences (run keep s arg plan).binds)
  bounds : ∀ entry ∈ (run keep s arg plan).binds, Bounds (run keep s arg plan).state entry.2

/-- Independent finite source syntax drives actual nested projections.
The ordinary modeling obligation is compositional; each model is
extended without changing any existing or explicitly protected name.
There is no recursion on the evaluator, solver, or demand-search tree. -/
theorem build {s : State} (keep : List Nat) (plan : Plan) (arg : Capture)
    (bounds : Bounds s arg) (read : Read s arg.lower arg.upper plan) : Builds s keep arg plan := by
  induction plan generalizing s arg with
  | capture binder =>
    refine ⟨refl s keep,.refl _,.capture,?_⟩
    intro entry present
    cases List.mem_singleton.mp present
    exact bounds
  | product e a b ih jh =>
    cases read with
    | product lo hi seenA seenB =>
      let t := ready s arg.center keep e
      let l := left s arg.center keep e
      let r := right s arg.center keep e
      have lift : Retains s t keep := pairs bounds (entails lo) (entails hi) keep
      obtain ⟨lBound,rBound⟩ := GeneralDeclarativeOpaqueIntervals328.bounds (s := s) arg.center keep e
      have before := ih l lBound (grows lift.grows seenA)
      have after := jh r (fits before.modeled.grows rBound)
        (grows before.modeled.grows (grows lift.grows seenB))
      have onward := chain before.modeled after.modeled
      refine ⟨chain lift onward,?_,?_,?_⟩
      · exact .trans (derives onward.grows (GeneralDeclarativeOpaqueIntervals328.actual (s := s) arg.center keep e))
          (.primitive (.cons (derives after.modeled.grows before.center) (.cons after.center .nil)))
      · simpa only [run,Plan.code,occurrences,List.map_append,List.append_nil,pair] using
          Walk.primitive (.cons before.ordered (.cons after.ordered .nil))
      · intro entry recorded
        change entry ∈ ((run keep t l a).binds ++ (run keep (run keep t l a).state r b).binds) at recorded
        rcases List.mem_append.mp recorded with first|last
        · exact fits after.modeled.grows (before.bounds entry first)
        · exact after.bounds entry last
  | tagged tag lo hi plan ih =>
    cases read with
    | tagged seenLo seenHi inside =>
      let t := GeneralDeclarativeOpaqueVariantNames328.ready s tag arg.center lo hi keep
      let a := GeneralDeclarativeOpaqueVariantNames328.names s arg.center lo hi keep
      have step : Retains s t keep := variants bounds (entails seenLo) (entails seenHi) keep
      have downstream := ih a (GeneralDeclarativeOpaqueVariantNames328.known_bounds s tag arg.center lo hi keep)
        (grows step.grows inside)
      exact ⟨chain step downstream.modeled,
        .trans (derives downstream.modeled.grows
          (GeneralDeclarativeOpaqueVariantNames328.reads_center s tag arg.center lo hi keep))
          (.variant downstream.center),.variant downstream.ordered,downstream.bounds⟩
  | invariant tag lo hi plan ih =>
    cases read with
    | invariant seenLo seenHi inside =>
      let t := GeneralDeclarativeOpaqueNominal328.ready s arg.center tag lo
      let a := GeneralDeclarativeOpaqueNominal328.point lo
      have step : Retains s t keep := GeneralDeclarativeOpaqueNominal328.retains bounds (entails seenLo) (entails seenHi)
      have downstream := ih a (GeneralDeclarativeOpaqueNominal328.point_bounded t lo)
        (grows step.grows inside)
      refine ⟨chain step downstream.modeled,
        .trans (derives downstream.modeled.grows (GeneralDeclarativeOpaqueNominal328.reads arg.center tag lo))
          (.nominal (.cons downstream.center .nil)),?_,downstream.bounds⟩
      simpa only [run,Plan.code,List.append_nil] using Walk.nominal (.cons downstream.ordered .nil)

end Yulang.GeneralDeclarativeOpaqueNested328
