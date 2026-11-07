import Yulang.CommonRoleClosedRecordResidual
import Yulang.CommonRoleIntervalRecordResidual

/-!
# Interval generation for determined closed record residuals

This separate encoding retains the exact-empty terminal of a closed spine.
It does not change the existing width-ended record interval component.
Both endpoints come from the same canonical subtraction. The interpretation
is the actual Common closed-record constructor used by the required and
optional observation theorems, rather than a producer-mask approximation.

The source spine must already be determined and closed. Head eligibility,
explicit-field payload matching and pending goals are not decided here.
-/

namespace Yulang.CommonRoleClosedIntervalRecordGeneration

open Core.PresenceGeneration (TyTerm Comp)
open CommonRoleCanonicalRows (Row capture)
open CommonRoleIntervalRecordResidual (Fields lowerFields upperFields)
open CommonRoleIntervals (Interval Fits Valid evaluate)
open CommonRoleIntervalGeneration (Argument)
open CommonPatternConcreteRecordTypes (recordTypeOf)
open PresenceNormalForm (Atom All)

def recordTerm : Row (TyTerm α) → TyTerm α
  | [] => .exactEmpty
  | (label, payload) :: rest => .record label payload (recordTerm rest)

/-- Literal interpretation in the Common closed record constructor. This
connects the generated syntax to the all-depth field/absence semantics. -/
theorem recordTerm_eval (assignment : α → Comp Common.model)
    (fields : Row (TyTerm α)) :
    (recordTerm fields).eval Common.model assignment =
      recordTypeOf (fun term => term.eval Common.model assignment) fields := by
  induction fields with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨label, payload⟩
      simp only [recordTerm, TyTerm.eval, recordTypeOf]
      exact congrArg (Common.record label (payload.eval Common.model assignment)) ih

end Yulang.CommonRoleClosedIntervalRecordGeneration
