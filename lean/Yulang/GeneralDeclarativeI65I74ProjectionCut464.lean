import Yulang.GeneralDeclarativeI65I74ProjectionAliasClass464
import Yulang.GeneralDeclarativeI65I74SplitEscape446

namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (State)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias)
open Yulang.GeneralDeclarativeI65.I72
open List410 (ExactEscapeWire)
open SplitEscape446 (splitCheck446 split_check_reflects_actual_rows446 pathsFromOne sameSide)

/-- Reuse a *before-state* finite escape wire. It never inserts a row, never
sources a shape from a model, and never decides issuer or source permission. -/
def checksNamedProjectionCut (s : State) (site : Nat) (term : Expr) (w : ExactEscapeWire) : Bool :=
  splitCheck446 s site w &&
    (match shapeOf term with
      | none => false
      | some h => h.children.all (fun n => decide (w.side n = 1)))

theorem finite_cut_implies_no_invented_or_lost_alias_cycle {s : State}
    {site : Nat} {term : Expr} {w : ExactEscapeWire}
    (ok : checksNamedProjectionCut s site term w = true) (v : Nat) :
    AliasCycle (extendedRows s ⟨site,term⟩) (observed (extendedRows s ⟨site,term⟩)) v ↔
      AliasCycle s (observed s) v := by
  have validate := Bool.and_eq_true_iff.mp ok
  have proof := split_check_reflects_actual_rows446.mp validate.1
  apply one_nonalias_raw_row_does_not_change_k2_under_original_class_no_return
  · intro n e
    have fail := validate.2
    rw [e] at fail
    cases fail
  · intro shape parsed n member near alias path
    have mark : w.side n = 1 := by
      have rows := validate.2
      rw [parsed] at rows
      exact of_decide_eq_true (List.all_eq_true.mp rows n member)
    have reaches : w.side near = 1 := pathsFromOne proof path mark
    have impossible := (sameSide proof alias).trans proof.rootZero
    rw [reaches] at impossible
    cases impossible

end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
