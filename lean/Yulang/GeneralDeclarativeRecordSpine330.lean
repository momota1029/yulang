import Yulang.GeneralDeclarativeOrderedRecord326
import Yulang.GeneralDeclarativeVisibleRecord326
import Yulang.GeneralDeclarativeTraceTransfer325
import Yulang.GeneralDeclarativeOpaqueTrace328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordSpine330
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeRecordResidual323 (withTail reconstruct_with_terminal permute_fields)
open GeneralDeclarativeRecordHead323 (selected_nodup)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarativeOrderedRecord326 (order to_permutation)
open CommonRoleCanonicalRows (Row normalize normalize_unique residual)
open GeneralDeclarativeRepeatedActual323 (eqAt)

/-- Inline constructor syntax can be read directly inside a
supported RHS. Its tail is either a genuine terminal (constructor
below) or a logical name whose own authorized spine can be followed.
A join or unknown tail never becomes a terminal by model equality. -/
inductive Terminal : Expr → Prop where
  | width : Terminal (.primitive .emptyRecord [])
  | exactEnd : Terminal (.primitive .exactEmpty [])

/-- A closed ordinary source spine follows authorized name equalities
and stored record prefixes. Payloads in buried fields can be arbitrary
ordinary expressions; no terminal is chosen from a model. -/
inductive Spine (s : State) : Nat → Row Expr → Expr → Prop where
  | width : Alias s root owner →
    (⟨owner,.primitive .emptyRecord []⟩ : Equation) ∈ s.equations →
    Spine s root [] (.primitive .emptyRecord [])
  | exactEnd : Alias s root owner →
    (⟨owner,.primitive .exactEmpty []⟩ : Equation) ∈ s.equations →
    Spine s root [] (.primitive .exactEmpty [])
  | cons : Alias s root owner →
    (⟨owner,.record key (.variable field) (.variable rest)⟩ : Equation) ∈ s.equations →
    Spine s rest row terminal → Spine s root ((key,.variable field)::row) terminal

  | inline : Alias s root owner → Terminal terminal →
    (⟨owner,withTail fields terminal⟩ : Equation) ∈ s.equations →
    Spine s root fields terminal
  | prefixed : Alias s root owner →
    (⟨owner,withTail front (.variable rest)⟩ : Equation) ∈ s.equations →
    Spine s rest suffix terminal → Spine s root (front ++ suffix) terminal

theorem tail_append (first last : Row Expr) (tail : Expr) :
    withTail first (withTail last tail) = withTail (first ++ last) tail := by
  induction first with
  | nil => rfl
  | cons f _ ih => simp only [withTail,List.cons_append,ih]

theorem prefix_derives {s : State} (front : Row Expr) (r : Derives s x y) :
    Derives s (withTail front x) (withTail front y) := by
  induction front with
  | nil => exact r
  | cons _ _ ih => exact .record (.refl _) ih

theorem ends {s : State} (seen : Spine s root fields terminal) : Terminal terminal := by
  induction seen with
  | width => exact .width
  | exactEnd => exact .exactEnd
  | inline _ t _ => exact t
  | cons _ _ _ ih | prefixed _ _ _ ih => exact ih

theorem assemble {s : State} (actual : Spine s root fields terminal) :
    Derives s (.variable root) (withTail fields terminal) := by
  induction actual with
  | width linked stored => exact .trans (.congruent (.variable linked)) (.row stored)
  | exactEnd linked stored => exact .trans (.congruent (.variable linked)) (.row stored)
  | cons linked stored _ tail =>
    exact .trans
      (.trans (.congruent (.variable linked)) (.row stored)) (.record (.refl _) tail)

  | inline linked _ stored => exact .trans (.congruent (.variable linked)) (.row stored)
  | @prefixed root owner front rest suffix terminal linked stored _ tail =>
    rw [← tail_append front suffix terminal]
    exact .trans (.trans (.congruent (.variable linked)) (.row stored)) (prefix_derives front tail)

theorem was_named {s : State} {p : Supported s done} (actual : Spine (restriction p) root fields terminal) :
    Derives s (.variable root) (withTail fields terminal) :=
  GeneralDeclarativeOrdinaryIncrease325.derives (GeneralDeclarativeOpaqueTrace328.ordinary_over_support p)
    (assemble actual)

theorem exact_subtraction {s : State} {p : Supported s done}
    (actual : Spine (restriction p) root fields terminal) (distinct : keys.Nodup)
    (sorted : order (normalize fields) keys = some chosen) :
    Entails s ⟨root,withTail chosen (withTail (residual keys (normalize fields)) terminal)⟩ := by
  intro m fit
  have raw := entails (was_named actual) m fit
  have canonical := visible_spine m fields terminal
  have split := reconstruct_with_terminal m (normalize fields) keys terminal (normalize_unique fields)
  have ordered := permute_fields m (withTail (residual keys (normalize fields)) terminal)
    (to_permutation distinct sorted) (selected_nodup _ _ (normalize_unique fields))
  exact eqv_trans raw (eqv_trans canonical (eqv_trans split ordered))

end Yulang.GeneralDeclarativeRecordSpine330
