import Yulang.CommonRoleClosedRecordComparison
import Yulang.CommonRoleStableRecordResidual
import Yulang.CommonRoleClosedIntervalRecordGeneration

/-!
# Finite ordinary checks for closed records with known field labels

The existing all-depth Common comparison theorem reduces a same-label closed
record comparison to the original first payload at every label. This module
performs that reduction in actual finite `tyLe` syntax. It never submits an
unsupported negative `exactEmpty` record directly to the ordinary solver.

Unknown or differing field sets remain outside this same-spine component.
Payload endpoints and their shared source slots are arbitrary and unchanged.
-/

namespace Yulang.CommonRoleClosedRecordInspection

open CommonRoleCanonicalRows (Row lookup)
open CommonRoleClosedRecordComparison (SameLabels checkSameLabels)
open CommonPatternConcreteRecordTypes (recordTypeOf)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

/-- Iterating the original first row is finite. Both lookups still use the
original rows, so a later duplicate cannot contribute its hidden payload. -/
def payloadChecks (first last : Row (TyTerm α)) : List (Atom α) :=
  first.filterMap fun entry => do
    let source ← lookup entry.1 first
    let target ← lookup entry.1 last
    pure (.tyLe source target)

theorem payload_checks_exact (assignment : α → Comp Common.model)
    (first last : Row (TyTerm α)) :
    All Common.model assignment (payloadChecks first last) ↔
      ∀ label source target, lookup label first = some source → lookup label last = some target →
        Common.Subtype (source.eval Common.model assignment) (target.eval Common.model assignment) := by
  constructor
  · intro model label source target sourceAt targetAt
    apply model (.tyLe source target)
    apply List.mem_filterMap.mpr
    exact ⟨(label, source), CommonRoleStableRecordResidual.lookup_member _ _ _ sourceAt,
      by simp [sourceAt, targetAt]⟩
  · intro compared atom member
    obtain ⟨entry, _, returned⟩ := List.mem_filterMap.mp member
    cases sourceAt : lookup entry.1 first with
    | none => simp [sourceAt] at returned
    | some source =>
        cases targetAt : lookup entry.1 last with
        | none => simp [sourceAt, targetAt] at returned
        | some target =>
            have same : Atom.tyLe source target = atom := by
              simpa [sourceAt, targetAt] using returned
            subst atom
            exact compared entry.1 source target sourceAt targetAt

def inspect (first last : Row (TyTerm α)) : Option (List (Atom α)) :=
  if checkSameLabels first last then some (payloadChecks first last) else none

/-- The finite label gate is included in the independent judgment. Its
failure is not claimed to decide general Common record subtyping. -/
theorem inspect_exact (assignment : α → Comp Common.model)
    (first last : Row (TyTerm α)) :
    (∃ atoms, inspect first last = some atoms ∧ All Common.model assignment atoms) ↔
      SameLabels first last ∧
        Common.Subtype (recordTypeOf (fun term => term.eval Common.model assignment) first)
          (recordTypeOf (fun term => term.eval Common.model assignment) last) := by
  by_cases same : checkSameLabels first last = true
  · have shape := (CommonRoleClosedRecordComparison.check_same_labels_exact first last).mp same
    constructor
    · rintro ⟨atoms, returned, models⟩
      have actual : payloadChecks first last = atoms := by simpa [inspect, same] using returned
      subst atoms
      exact ⟨shape, (CommonRoleClosedRecordComparison.subtype_lookup_exact _ _ _ _ shape).mpr
        ((payload_checks_exact assignment first last).mp models)⟩
    · rintro ⟨_, compared⟩
      refine ⟨payloadChecks first last, by simp [inspect, same], ?_⟩
      exact (payload_checks_exact assignment first last).mpr
        ((CommonRoleClosedRecordComparison.subtype_lookup_exact _ _ _ _ shape).mp compared)
  · have different : ¬ SameLabels first last := fun shape =>
      same ((CommonRoleClosedRecordComparison.check_same_labels_exact first last).mpr shape)
    simp [inspect, same, different]

end Yulang.CommonRoleClosedRecordInspection
