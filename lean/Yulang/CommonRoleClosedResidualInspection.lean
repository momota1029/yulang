import Yulang.CommonRoleClosedIntervalInspection

/-!
# Payload inspection of the actual canonical closed record remainder

The subtraction is the existing first-field-wins canonical capture. Once the
source spine and the requested spine are determined, the payload inspector
computes exactly the same four interval obligations as the existing whole
record generator. The additional finite label gate is stated explicitly.
-/

namespace Yulang.CommonRoleClosedResidualInspection

open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleCanonicalRows (capture)
open CommonRoleIntervalRecordResidual (Fields lowerFields upperFields)
open CommonRoleClosedRecordComparison (SameLabels)
open CommonRoleClosedIntervalInspection (reconcile interval)
open CommonRoleClosedIntervalRecordGeneration (recordTerm evaluated)

def argument (fields : Fields α) : CommonRoleIntervalGeneration.Argument α :=
  (recordTerm (lowerFields fields), recordTerm (upperFields fields))

theorem argument_eval (assignment : α → Comp Common.model) (fields : Fields α) :
    evaluated assignment (argument fields) = interval assignment fields := by
  simp only [evaluated, CommonRoleIntervals.evaluate, argument,
    CommonRoleIntervalGeneration.eval, interval,
    CommonRoleClosedIntervalRecordGeneration.recordTerm_eval]

def inspect (labels : List Nat) (fields requested : Fields α) : Option (List (Atom α)) :=
  reconcile (capture labels fields) requested

/-- The original endpoints are first subjected to the actual canonical
subtraction. No independently supplied residual or semantic centre is used. -/
theorem inspect_exact (assignment : α → Comp Common.model)
    (labels : List Nat) (fields requested : Fields α) :
    (∃ atoms, inspect labels fields requested = some atoms ∧ All Common.model assignment atoms) ↔
      SameLabels (capture labels fields) requested ∧
        CommonRoleClosedIntervalRecordGeneration.Compatible assignment labels fields
          (argument requested) := by
  rw [inspect, CommonRoleClosedIntervalInspection.reconcile_exact]
  have residual : CommonRoleClosedIntervalRecordGeneration.bounds labels fields =
      argument (capture labels fields) := rfl
  simp only [CommonRoleClosedIntervalRecordGeneration.Compatible, residual, argument_eval,
    CommonRoleClosedIntervalInspection.Compatible]

/-- The new finite payload output is a faithful lowering of the existing
whole-record interval generator, on the explicitly computed same-spine domain. -/
theorem inspect_generation_exact (assignment : α → Comp Common.model)
    (labels : List Nat) (fields requested : Fields α) :
    (∃ atoms, inspect labels fields requested = some atoms ∧ All Common.model assignment atoms) ↔
      SameLabels (capture labels fields) requested ∧
        All Common.model assignment
          (CommonRoleClosedIntervalRecordGeneration.generate labels fields (argument requested)) := by
  rw [inspect_exact, CommonRoleClosedIntervalRecordGeneration.generate_exact]

end Yulang.CommonRoleClosedResidualInspection
