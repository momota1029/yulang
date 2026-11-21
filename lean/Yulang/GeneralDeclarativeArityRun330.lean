import Yulang.GeneralDeclarativeArityPlan330
import Yulang.GeneralDeclarativeOpaqueNested328

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeArityRun330
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueConserve328 (Retains refl chain pairs variants)
open GeneralDeclarativeOpaqueIntervals328 (left right ready)
open GeneralDeclarativeArityPlan330 (Plan Plans Reads ReadsFields grow growFields)
open GeneralDeclarativeOpaqueNested328 (Named occurrences)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeGrowth327 (Extends derives fits)
open GeneralDeclarativeEqualities322 (Derives Forest entails)
open GeneralDeclarativePairCenters326 (pair)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeTermWalk322 (Walk WalkMany)

structure NamedFields where
  state : State
  forms : List Expr
  binds : List (Nat × Capture)

mutual
def run (keep : List Nat) (s : State) (arg : Capture) : Plan → Named
  | .capture n => ⟨s,.variable arg.center,[(n,arg)]⟩
  | .pair e a b =>
    let t := ready s arg.center keep e
    let x := run keep t (left s arg.center keep e) a
    let y := run keep x.state (right s arg.center keep e) b
    ⟨y.state,pair x.form y.form,x.binds ++ y.binds⟩
  | .tagged tag lo hi node =>
    let t := GeneralDeclarativeOpaqueVariantNames328.ready s tag arg.center lo hi keep
    let x := run keep t (GeneralDeclarativeOpaqueVariantNames328.names s arg.center lo hi keep) node
    ⟨x.state,.variant tag x.form,x.binds⟩
  | .nominal tag _ fields =>
    let t := GeneralDeclarativeArityNominal330.ready s arg.center tag fields.names
    let x := runFields keep t fields
    ⟨x.state,.nominal tag x.forms,x.binds⟩
def runFields (keep : List Nat) (s : State) : Plans → NamedFields
  | .nil => ⟨s,[],[]⟩
  | .cons n one rest =>
    let left := run keep s (point n) one
    let rest := runFields keep left.state rest
    ⟨rest.state,left.form :: rest.forms,left.binds ++ rest.binds⟩
end

structure Builds (keep : List Nat) (s : State) (arg : Capture) (plan : Plan) : Prop where
  modeled : Retains s (run keep s arg plan).state keep
  center : Derives (run keep s arg plan).state (.variable arg.center) (run keep s arg plan).form
  walks : Walk .actual (run keep s arg plan).form plan.code (occurrences (run keep s arg plan).binds)
  bounds : ∀ entry ∈ (run keep s arg plan).binds, Bounds (run keep s arg plan).state entry.2

structure BuildsFields (keep : List Nat) (s : State) (fields : Plans) : Prop where
  modeled : Retains s (runFields keep s fields).state keep
  centers : Forest (runFields keep s fields).state (fields.names.map Expr.variable) (runFields keep s fields).forms
  walks : WalkMany .actual (runFields keep s fields).forms fields.codes (occurrences (runFields keep s fields).binds)
  bounds : ∀ entry ∈ (runFields keep s fields).binds, Bounds (runFields keep s fields).state entry.2

theorem forest_move {s t : State} (h : Extends s t) (p : Forest s xs ys) : Forest t xs ys := by
  induction xs generalizing ys with
  | nil => cases p; exact .nil
  | cons a rest ih =>
    cases p with
    | cons here tail => exact .cons (derives h here) (ih tail)

mutual
theorem build (keep : List Nat) {s : State} (arg : Capture) (plan : Plan)
    (bounds : Bounds s arg) (visited : Reads s arg.lower arg.upper plan) : Builds keep s arg plan := by
  cases plan with
  | capture binder =>
    refine ⟨refl s keep,.refl _,.capture,?_⟩
    intro entry known
    cases List.mem_singleton.mp known
    exact bounds
  | pair e a b =>
    cases visited with
    | pair lo hi seenA seenB =>
      let t := ready s arg.center keep e
      let l := left s arg.center keep e
      let r := right s arg.center keep e
      have lift : Retains s t keep := pairs bounds (entails lo) (entails hi) keep
      obtain ⟨lBound,rBound⟩ := GeneralDeclarativeOpaqueIntervals328.bounds (s := s) arg.center keep e
      have before := build keep l a lBound (grow lift.grows seenA)
      have after := build keep r b (fits before.modeled.grows rBound)
        (grow before.modeled.grows (grow lift.grows seenB))
      have onward := chain before.modeled after.modeled
      refine ⟨chain lift onward,?_,?_,?_⟩
      · exact .trans (derives onward.grows (GeneralDeclarativeOpaqueIntervals328.actual (s := s) arg.center keep e))
          (.primitive (.cons (derives after.modeled.grows before.center) (.cons after.center .nil)))
      · simpa only [run,Plan.code,occurrences,List.map_append,List.append_nil,pair] using
          Walk.primitive (.cons before.walks (.cons after.walks .nil))
      · intro entry recorded
        change entry ∈ ((run keep t l a).binds ++ (run keep (run keep t l a).state r b).binds) at recorded
        rcases List.mem_append.mp recorded with first|last
        · exact fits after.modeled.grows (before.bounds entry first)
        · exact after.bounds entry last
  | tagged tag lo hi plan =>
    cases visited with
    | tagged seenLo seenHi inside =>
      let t := GeneralDeclarativeOpaqueVariantNames328.ready s tag arg.center lo hi keep
      let a := GeneralDeclarativeOpaqueVariantNames328.names s arg.center lo hi keep
      have step : Retains s t keep := variants bounds (entails seenLo) (entails seenHi) keep
      have downstream := build keep a plan (GeneralDeclarativeOpaqueVariantNames328.known_bounds s tag arg.center lo hi keep)
        (grow step.grows inside)
      exact ⟨chain step downstream.modeled,
        .trans (derives downstream.modeled.grows
          (GeneralDeclarativeOpaqueVariantNames328.reads_center s tag arg.center lo hi keep))
          (.variant downstream.center),.variant downstream.walks,downstream.bounds⟩
  | nominal tag _ fields =>
    cases visited with
    | nominal lowRow highRow inside =>
      let t := GeneralDeclarativeArityNominal330.ready s arg.center tag fields.names
      have step : Retains s t keep := GeneralDeclarativeArityNominal330.retains keep bounds (entails lowRow) (entails highRow)
      have downstream := buildFields keep fields (growFields step.grows inside)
      exact ⟨chain step downstream.modeled,
        .trans (derives downstream.modeled.grows
          (GeneralDeclarativeArityNominal330.reads (s := s) arg.center tag fields.names))
          (.nominal downstream.centers),.nominal downstream.walks,downstream.bounds⟩
termination_by sizeOf plan

theorem buildFields (keep : List Nat) {s : State} (fields : Plans)
    (visited : ReadsFields s fields) : BuildsFields keep s fields := by
  cases fields with
  | nil => exact ⟨refl s keep,.nil,.nil,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons n one rest =>
    cases visited with
    | cons first last =>
      have oneSeen := build keep (point n) one (point_bounded s n) first
      have restSeen := buildFields keep rest (growFields oneSeen.modeled.grows last)
      refine ⟨chain oneSeen.modeled restSeen.modeled,
        .cons (derives restSeen.modeled.grows oneSeen.center) restSeen.centers,?_,?_⟩
      · simpa only [runFields,Plans.codes,occurrences,List.map_append] using WalkMany.cons oneSeen.walks restSeen.walks
      · intro entry recorded
        change entry ∈ (run keep s (point n) one).binds ++
          (runFields keep (run keep s (point n) one).state rest).binds at recorded
        rcases List.mem_append.mp recorded with l|r
        · exact fits restSeen.modeled.grows (oneSeen.bounds entry l)
        · exact restSeen.bounds entry r
termination_by sizeOf fields
end

end Yulang.GeneralDeclarativeArityRun330
