import Yulang.GeneralDeclarativeRecordSpine330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineSpine331
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeRecordSpine330 (Spine Terminal assemble)
open GeneralDeclarativeRecordResidual323 (withTail reconstruct_with_terminal permute_fields)
open GeneralDeclarativeRecordHead323 (selected_nodup)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralDeclarativeOrderedRecord326 (order to_permutation)
open GeneralDeclarativeOpaqueTrace328 (ordinary_over_support)
open GeneralDeclarativeOrdinaryIncrease325 (derives)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonRoleCanonicalRows (Row normalize normalize_unique residual)

/-- A record remainder is computed from literal syntax or already
authorized rows. An opaque expression is not an empty row; a named
tail contributes only if there is a supported closed spine for it. -/
inductive Closed (s : State) : Expr → Row Expr → Expr → Prop where
  | terminal : Terminal raw → Closed s raw [] raw
  | field : Closed s next rest terminal →
    Closed s (.record key payload next) ((key,payload)::rest) terminal
  | name : Spine s n row terminal → Closed s (.variable n) row terminal

theorem spell {s : State} (observed : Closed s input raw terminal) :
    Derives s input (withTail raw terminal) := by
  induction observed with
  | terminal => exact .refl _
  | field _ ih => exact .record (.refl _) ih
  | name yes => exact assemble yes

theorem ends {s : State} (observed : Closed s input raw terminal) : Terminal terminal := by
  induction observed with
  | terminal known => exact known
  | field _ ih => exact ih
  | name yes => exact GeneralDeclarativeRecordSpine330.ends yes

theorem split {s : State} {p : Supported s done}
    (observed : Closed (restriction p) input raw terminal) (different : keys.Nodup)
    (ordered : order (normalize raw) keys = some taken) (m) (accepted : Models s m) :
    eqAt m input (withTail taken (withTail (residual keys (normalize raw)) terminal)) := by
  have unfolded := semantic (derives (ordinary_over_support p) (spell observed)) m accepted
  have clean := visible_spine m raw terminal
  have split := reconstruct_with_terminal m (normalize raw) keys terminal (normalize_unique raw)
  have perm := permute_fields m (withTail (residual keys (normalize raw)) terminal)
    (to_permutation different ordered) (selected_nodup _ _ (normalize_unique raw))
  exact eqv_trans unfolded (eqv_trans clean (eqv_trans split perm))

end Yulang.GeneralDeclarativeInlineSpine331
