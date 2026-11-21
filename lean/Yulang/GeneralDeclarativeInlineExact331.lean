import Yulang.GeneralDeclarativeInlineEndpoint331
import Yulang.GeneralDeclarativeRecordConsumption330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineExact331
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeInlineTrace331 (Read Args Fields TailCode)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order exact_order)
open GeneralDeclarativeRecordConsumption330 (read_field)
open GeneralDeclarativeRecordPayloads330 (Field)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open CommonRoleCanonicalRows (Row normalize normalize_unique)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem field_labels {s : State} (f : Fields s mode picked written uses) :
    picked.map Prod.fst = written.map Prod.fst := by
  induction picked generalizing written uses with
  | nil => cases f; rfl
  | cons hd tl ih =>
    cases f with
    | cons _ more =>
      simp only [List.map_cons,ih more]

theorem exact_keys {s : State} (f : Fields s mode picked written uses)
    (showed : order (normalize raw) keys = some picked) :
    written.map Prod.fst = keys :=
  (field_labels f).symm.trans (exact_order (normalize_unique raw) showed).1

/-- A binder records the given expression, not an equivalent alias
or a term selected using the eventual dictionary. The nonempty
record guard rules out misusing a field-free decomposition for it. -/
theorem capture_exact {s : State} (yes : Read s mode raw code uses) :
    ∀ key, code = .variable key → uses = [⟨key,mode,raw⟩] := by
  refine Read.rec
    (motive_1 := fun mode raw code uses _ => ∀ key, code = .variable key → uses = [⟨key,mode,raw⟩])
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ yes
  · intro mode raw binder key h
    cases h
    rfl
  · intro _ _ _ _ _ _ notBinder _ _ _ _ key h
    exact False.elim (notBinder key h)
  · intro _ _ _ _ _ _ _ _ h; cases h
  · intro _ _ _ _ _ _ _ _ h; cases h
  · intro _ _ _ _ _ _ _ _ h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
  · intro _ _ _ keys _ _ written _ _ _ _ _ nonempty printed field _ _ _ _ key h
    cases written with
    | nil => exact False.elim (nonempty ((exact_keys field printed).symm))
    | cons hd tl =>
      change Expr.record _ _ _ = Expr.variable key at h
      cases h
  · intro; trivial
  · intros; trivial
  · intro; trivial
  · intros; trivial

theorem fixed_record_tail {s : State} (visible : Closed s raw fs terminal) (keys : names.Nodup)
    (nonempty : names ≠ []) (ordered : order (normalize fs) names = some taken)
    (payloads : Fields s mode taken written uses) :
    Read s mode raw (withTail written (.variable tailBinder))
      (uses ++ [⟨tailBinder,mode,tailExpr fs names terminal⟩]) :=
  .record visible keys nonempty ordered payloads .binder .capture

/-- The independent endpoint judgment does not examine the centre.
A new admissible centre for the same endpoints has exactly the same
positive probes; the different actual read is handled later. -/
theorem replace_center {s : State} {a b : Capture} (given : Matches s c i a pat)
    (fit : Bounds s b) (lo : a.lower = b.lower) (hi : a.upper = b.upper) :
    Matches s c i b pat := by
  obtain ⟨_,code,first,last,printed,low,high⟩ := given
  exact ⟨fit,code,first,last,printed,lo ▸ low,hi ▸ high⟩

end Yulang.GeneralDeclarativeInlineExact331
