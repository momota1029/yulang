import Yulang.GeneralDeclarativeOpaqueNominal328
import Yulang.GeneralDeclarativeTraceTransfer325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeArityNominal330
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeEntailment320 (Entails appendFacts conservative_append)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeGrowth327 (facts)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeTraceTransfer325 (ordinary)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open CommonNominalFullCarrier (Ty subtype_trans)
open GeneralNominalCommonBridge (Assignment)

def code (tag : Nat) (args : List Nat) : Expr := .nominal tag (args.map Expr.variable)
def row (root tag : Nat) (args : List Nat) : Equation := ⟨root,code tag args⟩
def ready (s : State) (root tag : Nat) (args : List Nat) : State := appendFacts s [row root tag args]

theorem value_shape (m : Assignment) (args : List Nat) :
    values (environment m) .actual (args.map Expr.variable) = args.map fun n => (m n).1 := by
  induction args with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons,values,value,environment,ih]

/-- The lower endpoint determines every actual invariant parameter,
independently of arity. The input carries upper and lower name lists,
not an identification of either interval endpoint with the center. -/
theorem truth {s : State} (fits : Bounds s arg) (lo : Entails s (row arg.lower tag args))
    (hi : Entails s (row arg.upper tag other)) :
    Entails s (row arg.center tag args) := by
  intro m fit
  have first := lo m fit
  have last := hi m fit
  have inRange := bounds_sound fits m fit
  unfold GeneralDeclarativeEntailment320.Holds row code at first last ⊢
  simp only [value,value_shape] at first last ⊢
  exact (GeneralNominalIntervalLaws.nominal_sandwich tag tag _ _ (m arg.center).1
    (subtype_trans first.2 inRange.1) (subtype_trans inRange.2 last.1)).1

theorem retains {s : State} (keep : List Nat) (fits : Bounds s arg)
    (lo : Entails s (row arg.lower tag args)) (hi : Entails s (row arg.upper tag other)) :
    Retains s (ready s arg.center tag args) keep := by
  refine ⟨facts _ _,?_⟩
  intro m fit
  have h : ∀ e ∈ [row arg.center tag args], Entails s e := by
    intro e one
    cases List.mem_singleton.mp one
    exact truth fits lo hi
  exact ⟨m,(conservative_append h m).mpr fit,fun _ _ => rfl⟩

theorem reads {s : State} (root tag : Nat) (args : List Nat) :
    Derives (ready s root tag args) (.variable root) (code tag args) :=
  .row (List.mem_append_right _ List.mem_cons_self)

theorem traced {s : State} {p : Supported s done} (h : Trace (restriction p) mode root (.nominal tag target) uses) :
    ∃ actual, Derives s (.variable root) (code tag actual) ∧ TraceArgs (restriction p) .actual actual target uses := by
  cases h with
  | nominal aliased stored args =>
    exact ⟨_,GeneralDeclarativeOrdinaryIncrease325.derives (GeneralDeclarativeOpaqueTrace328.ordinary_over_support p)
      (.trans (.congruent (.variable aliased)) (.row stored)),args⟩

end Yulang.GeneralDeclarativeArityNominal330
