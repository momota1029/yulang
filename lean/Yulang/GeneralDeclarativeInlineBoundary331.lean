import Yulang.GeneralDeclarativeInlineFieldProducer331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineBoundary331
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeRecordSpine330 (Spine was_named ends head_known)
open GeneralDeclarativeRecordPayloads330 (Field visible has_field)
open GeneralDeclarativeInlineNegative331 (missing_projection)
open GeneralDeclarativeLowerKnown321 (Knows)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_trans)
open CommonRoleCanonicalRows (lookup)

theorem visible_implies_known {s : State} (take : Field key raw payload)
    (actual : Closed s (.variable name) raw terminal) : ∃ tag, Knows s name tag := by
  cases actual with
  | terminal tag => cases tag
  | name read =>
    cases raw with
    | nil => cases take
    | cons h t =>
      exact ⟨_,head_known read rfl⟩

/-- A required field can occur anywhere in a candidate's whole
record layout. A missing genuine supported closed lower field
precludes that layout in every current model, not merely when
the proposed field is printed first. -/
theorem missing_blocks_layout {s : State} {p : Supported s done}
    (box : Bounds s arg) (lower : Spine (restriction p) arg.lower old terminal)
    (absent : lookup key old = none) (must : Field key proposed payload) (tail)
    (m : Assignment) (valid : Models s m) :
    ¬eqAt m (.variable arg.center) (withTail proposed tail) := by
  intro current
  have lowerRead := semantic (was_named lower) m valid
  have step := subtype_trans lowerRead.2 (subtype_trans (bound_sound m valid.1 box.1) current.1)
  obtain ⟨_,found⟩ := has_field (visible must tail m) step
  rw [missing_projection key m old (ends lower) absent] at found
  cases found

end Yulang.GeneralDeclarativeInlineBoundary331
