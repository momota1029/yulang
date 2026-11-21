import Yulang.GeneralDeclarativeInlineGround331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlinePending331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeInlineLineage331 (Trail)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeInlineGround331 (Native sourcesOnly actual_source_row origin_path)
open GeneralDeclarativeRecordSpine330 (Spine)

/-- A source-only view with no rows cannot build a record spine by
following a name, even if ordinary intervals and pending rows elsewhere
make that name look equivalent to a known shape. -/
theorem no_spine {s : State} (empty : s.equations = []) (spine : Spine s name raw terminal) : False := by
  cases spine with
  | width _ stored | exactEnd _ stored | cons _ stored _ | inline _ _ stored | prefixed _ stored _ =>
    rw [empty] at stored
    cases stored

theorem no_closed_name {s : State} (empty : s.equations = [])
    (closed : Closed s (.variable name) raw terminal) : False := by
  cases closed with
  | terminal term => cases term
  | name known => exact no_spine empty known

theorem not_from_unknown {s : State} (empty : s.equations = []) (way : Trail s a b) :
    ∀ n, a = .variable n → b = .variable n := by
  induction way with
  | self => exact fun _ h => h
  | step _ _ before after => exact fun n h => after n (before n h)
  | expose _ stored =>
    rw [empty] at stored
    cases stored
  | primitive _ | nominal _ | variant | joinLeft | joinRight =>
    intro _ impossible
    cases impossible
  | selected closed _ _ | residual closed _ =>
    intro n h
    cases h
    exact False.elim (no_closed_name empty closed)

theorem no_source_only {s : State} {p : Supported s done}
    (none : ∀ row, ¬p.derivesFrom row .source) : (restriction (sourcesOnly p)).equations = [] := by
  cases eqs : (restriction (sourcesOnly p)).equations with
  | nil => rfl
  | cons row last =>
    have member := (show row ∈ (restriction (sourcesOnly p)).equations by rw [eqs]; exact List.mem_cons_self)
    exact False.elim (none row (actual_source_row.mp member))

/-- If the original branch has only ordinary output-origin equations,
no fresh name obtains a fabricated source witness. This remains true
even if the same equations were used in a successful model receipt. -/
theorem no_pending_promotion {s : State} {p : Supported s done}
    (none : ∀ row, ¬p.derivesFrom row .source) :
    ¬Native p arg keep uses row := by
  rintro ⟨stored,code,trace⟩
  obtain ⟨loc,_,_,complex,walk⟩ := origin_path trace stored
  exact complex _ (not_from_unknown (no_source_only none) walk _ rfl)

end Yulang.GeneralDeclarativeInlinePending331
