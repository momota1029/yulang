import Yulang.GeneralDeclarativeRecordPayloads330
import Yulang.GeneralDeclarativeInlineExact331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineNegative331
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativeRecordSpine330 (Spine Terminal was_named ends)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeRecordChannel330 (project shows addTrivial)
open GeneralDeclarativeRecordIntervals330 (direct)
open GeneralDeclarativeRecordPayloads330 (has_field)
open CommonNominalFullCarrier (Ty Equivalent record subtype_trans)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleCanonicalRows (Row lookup normalize lookup_normalize)
open GeneralDeclarativeOrderedRecord326 (order)

theorem missing_projection (key : Nat) (m : Assignment) (raw : Row Expr)
    (closed : Terminal terminal) (absent : lookup key raw = none) :
    project key false [] (value (environment m) .actual (withTail raw terminal)) = none := by
  induction raw with
  | nil => cases closed <;> rfl
  | cons head tail ih =>
    rcases head with ⟨label,payload⟩
    by_cases same : key = label
    · subst label
      simp [lookup] at absent
    · have later : lookup key tail = none := by simpa [lookup,same] using absent
      simp [withTail,value,record,project,shows,same,addTrivial,ih later]

/-- Genuine negative evidence: a supported closed lower endpoint
which lacks the required key is incompatible with an actual centre
having that required record head. This is not the negation of an
operational observer and is not a priority over waiting candidates. -/
theorem lower_excludes_required {s : State} {p : Supported s done}
    (box : Bounds s arg) (lower : Spine (restriction p) arg.lower raw terminal)
    (missing : lookup key raw = none) (m : Assignment) (valid : Models s m) :
    ∀ payload rest, ¬Equivalent (m arg.center).1 (record key payload rest) := by
  intro payload tail wants
  have low := semantic (was_named lower) m valid
  have upper := subtype_trans (bound_sound m valid.1 box.1) wants.1
  have below := subtype_trans low.2 upper
  obtain ⟨there,h⟩ := has_field (direct key false payload tail) below
  rw [missing_projection key m raw (ends lower) missing] at h
  cases h

/-- The negative conclusion is about the *first required key missing*
from the real normalized source. In contrast, from merely an observer
returning none, with no supported closed spine, no clash is inferred. -/
theorem absent_requested {s : State} {p : Supported s done}
    (box : Bounds s arg) (lower : Spine (restriction p) arg.lower raw terminal)
    (missing : lookup key (normalize raw) = none) (m : Assignment) (valid : Models s m) :
    ∀ payload rest, ¬Equivalent (m arg.center).1 (record key payload rest) :=
  lower_excludes_required box lower ((lookup_normalize raw key).symm.trans missing) m valid

end Yulang.GeneralDeclarativeInlineNegative331
