import Yulang.GeneralDeclarativeTaggedSources340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedPatch340
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTaggedSources340 (BoundsRead entail)
open GeneralDeclarativePairNames326 (Span Defines generated projection keepNames)
open GeneralDeclarativeOpaqueConserve328 (Retains chain variants)
open GeneralDeclarativeOpaqueVariantNames328 (ready names reads_center known_bounds)
open GeneralDeclarativeGrowth327 (Extends facts restrict fits)
open GeneralDeclarativeEntailment320 (Entails Holds model_append)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm variant_congr)

def extra (arg : Capture) (keep : List Nat) := arg.lower :: arg.center :: arg.upper :: keep

def ends (low high : Expr) : Span := ⟨low,low,high⟩

abbrev before (s : State) (a : Capture) (low high : Expr) (keep : List Nat) :=
  GeneralDeclarativePairNames326.appended s (extra a keep) (ends low high) (ends low high)

abbrev aliases (s : State) (a : Capture) (low high : Expr) (keep : List Nat) :=
  GeneralDeclarativePairNames326.first s (extra a keep) (ends low high) (ends low high)

abbrev prepared (s : State) (a : Capture) (tag : Nat) (low high : Expr) (keep : List Nat) :=
  let ids := aliases s a low high keep
  ready (before s a low high keep) tag a.center ids.lower ids.upper keep

abbrev captured (s : State) (a : Capture) (_tag : Nat) (low high : Expr) (keep : List Nat) :=
  let ids := aliases s a low high keep
  names (before s a low high keep) a.center ids.lower ids.upper keep

theorem pre_retains (s : State) (a : Capture) (low high : Expr) (keep : List Nat) :
    Retains s (before s a low high keep) keep := by
  refine ⟨facts _ _,?_⟩
  intro m fit
  obtain ⟨n,valid,old⟩ := (projection s (extra a keep) (ends low high) (ends low high) m).mp fit
  refine ⟨n,valid,fun v used => old v ?_⟩
  rcases List.mem_append.mp used with earlier|named
  · exact List.mem_append_left _ earlier
  · exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ named))))

theorem bounded_endpoint {s : State} {p : Supported s done} (seen : BoundsRead p a tag low high)
    (keep : List Nat) :
    Entails (before s a low high keep) ⟨a.lower,.variant tag (.variable (aliases s a low high keep).lower)⟩ ∧
    Entails (before s a low high keep) ⟨a.upper,.variant tag (.variable (aliases s a low high keep).upper)⟩ := by
  have actual := (generated s (extra a keep) (ends low high) (ends low high)).1
  constructor
  · intro m fit
    exact eqv_trans (entail seen.lower m ((model_append m).mp fit).1)
      (variant_congr tag (eqv_symm (semantic actual.1 m fit)))
  · intro m fit
    exact eqv_trans (entail seen.upper m ((model_append m).mp fit).1)
      (variant_congr tag (eqv_symm (semantic actual.2.2 m fit)))

/-- Joined lower and upper authored payloads produce one fresh bounded
capture, whose center denotes the actual whole payload reconstructed
from the real argument model, not either endpoint. Temporary pure
definitions remain ordinary rows and do not become authored support. -/
theorem patch {s : State} {p : Supported s done} (seen : BoundsRead p a tag low high) (keep : List Nat) :
    Retains s (prepared s a tag low high keep) keep ∧
      Bounds (prepared s a tag low high keep) (captured s a tag low high keep) ∧
      Derives (prepared s a tag low high keep) (.variable a.center)
        (.variant tag (.variable (captured s a tag low high keep).center)) := by
  have first := pre_retains s a low high keep
  have read := bounded_endpoint seen keep
  exact ⟨chain first (variants (fits first.grows seen.interval) read.1 read.2 keep),
    known_bounds .., reads_center ..⟩

end Yulang.GeneralDeclarativeTaggedPatch340
