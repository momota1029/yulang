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

/-- A closed ordinary source spine follows only authorized name
equalities and actual row records. There is no open-fallback case;
an unnamed or genuinely unknown terminal cannot produce a spine. -/
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

theorem assemble {s : State} (actual : Spine s root fields terminal) :
    Derives s (.variable root) (withTail fields terminal) := by
  induction actual with
  | width linked stored => exact .trans (.congruent (.variable linked)) (.row stored)
  | exactEnd linked stored => exact .trans (.congruent (.variable linked)) (.row stored)
  | cons linked stored _ tail =>
    exact .trans
      (.trans (.congruent (.variable linked)) (.row stored)) (.record (.refl _) tail)

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
