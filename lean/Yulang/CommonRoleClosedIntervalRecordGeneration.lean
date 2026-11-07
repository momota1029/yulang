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

def bounds (labels : List Nat) (fields : Fields α) : Argument α :=
  (recordTerm (lowerFields (capture labels fields)),
    recordTerm (upperFields (capture labels fields)))

def evaluated (assignment : α → Comp Common.model) (argument : Argument α) :
    Interval Common.Ty := evaluate (CommonRoleIntervalGeneration.eval assignment) argument

def Compatible (assignment : α → Comp Common.model) (labels : List Nat)
    (fields : Fields α) (requested : Argument α) : Prop :=
  Valid (evaluated assignment (bounds labels fields)) ∧
    Valid (evaluated assignment requested) ∧
    Common.Subtype (evaluated assignment (bounds labels fields)).1
      (evaluated assignment requested).2 ∧
    Common.Subtype (evaluated assignment requested).1
      (evaluated assignment (bounds labels fields)).2

def generate (labels : List Nat) (fields : Fields α) (requested : Argument α) :
    List (Atom α) :=
  CommonRoleIntervalGeneration.generate [bounds labels fields, requested]

/-- Both self checks and both cross checks for the actual computed closed
residual. The proof's semantic membership witness is not a head substitution
chosen by the generator, which emits only ordinary finite comparison atoms. -/
theorem generate_exact (assignment : α → Comp Common.model)
    (labels : List Nat) (fields : Fields α) (requested : Argument α) :
    All Common.model assignment (generate labels fields requested) ↔
      Compatible assignment labels fields requested := by
  have generated : All Common.model assignment (generate labels fields requested) ↔
      ∃ actual, Fits (evaluated assignment (bounds labels fields)) actual ∧
        Fits (evaluated assignment requested) actual := by
    unfold generate
    rw [CommonRoleIntervalGeneration.generate_real_argument_exact]
    simp [evaluated]
  rw [generated]
  exact (exists_congr fun actual =>
    (CommonRoleIntervals.fits_merge _ _ actual).symm).trans
      ((CommonRoleIntervals.valid_iff_nonempty _).symm.trans
        (CommonRoleIntervals.valid_merge_exact _ _))

end Yulang.CommonRoleClosedIntervalRecordGeneration
