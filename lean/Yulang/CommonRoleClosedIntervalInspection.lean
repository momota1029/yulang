import Yulang.CommonRoleClosedRecordInspection

/-!
# All four centreless interval checks on determined closed record spines

The label gate is computed from the original finite spines. The output is
four finite lists of original payload comparisons: both self-consistency
checks and both cross directions. Each uses the same first-field lookup.
No type between the endpoints is selected or stored.
-/

namespace Yulang.CommonRoleClosedIntervalInspection

open CommonRoleCanonicalRows (Row lookup capture)
open CommonRoleClosedRecordComparison (SameLabels checkSameLabels)
open CommonRoleIntervalRecordResidual (Fields mapPayload lowerFields upperFields)
open CommonRoleClosedRecordInspection (payloadChecks payload_checks_exact)
open CommonPatternConcreteRecordTypes (recordTypeOf)
open CommonRoleIntervals (Interval Valid)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

theorem lookup_map (label : Nat) (map : A → B) (fields : Row A) :
    lookup label (mapPayload map fields) = (lookup label fields).map map := by
  induction fields with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨current, payload⟩
      by_cases same : label = current
      · simp [lookup, mapPayload, same]
      · simpa [lookup, mapPayload, same] using ih

theorem same_labels_map (firstMap : A → C) (lastMap : B → D)
    (first : Row A) (last : Row B) :
    SameLabels (mapPayload firstMap first) (mapPayload lastMap last) ↔ SameLabels first last := by
  simp only [SameLabels, lookup_map, Option.isSome_map]

def interval (assignment : α → Comp Common.model) (fields : Fields α) : Interval Common.Ty :=
  (recordTypeOf (fun term => term.eval Common.model assignment) (lowerFields fields),
    recordTypeOf (fun term => term.eval Common.model assignment) (upperFields fields))

def Compatible (assignment : α → Comp Common.model) (first last : Fields α) : Prop :=
  Valid (interval assignment first) ∧ Valid (interval assignment last) ∧
    Common.Subtype (interval assignment first).1 (interval assignment last).2 ∧
    Common.Subtype (interval assignment last).1 (interval assignment first).2

def checks (first last : Fields α) : List (Atom α) :=
  payloadChecks (lowerFields first) (upperFields first) ++
    (payloadChecks (lowerFields last) (upperFields last) ++
      (payloadChecks (lowerFields first) (upperFields last) ++
        payloadChecks (lowerFields last) (upperFields first)))

private theorem payload_subtype_exact (assignment : α → Comp Common.model)
    (first last : Row (TyTerm α)) (shape : SameLabels first last) :
    All Common.model assignment (payloadChecks first last) ↔
      Common.Subtype (recordTypeOf (fun term => term.eval Common.model assignment) first)
        (recordTypeOf (fun term => term.eval Common.model assignment) last) :=
  (payload_checks_exact assignment first last).trans
    (CommonRoleClosedRecordComparison.subtype_lookup_exact _ _ _ _ shape).symm

theorem checks_exact (assignment : α → Comp Common.model) (first last : Fields α)
    (shape : SameLabels first last) :
    All Common.model assignment (checks first last) ↔ Compatible assignment first last := by
  have firstShape : SameLabels (lowerFields first) (upperFields first) :=
    (same_labels_map _ _ first first).mpr (fun _ => rfl)
  have lastShape : SameLabels (lowerFields last) (upperFields last) :=
    (same_labels_map _ _ last last).mpr (fun _ => rfl)
  have forward : SameLabels (lowerFields first) (upperFields last) :=
    (same_labels_map _ _ first last).mpr shape
  have backward : SameLabels (lowerFields last) (upperFields first) :=
    (same_labels_map _ _ last first).mpr (fun label => (shape label).symm)
  simp only [checks, PresenceNormalForm.all_append,
    payload_subtype_exact assignment _ _ firstShape,
    payload_subtype_exact assignment _ _ lastShape,
    payload_subtype_exact assignment _ _ forward,
    payload_subtype_exact assignment _ _ backward]
  rfl

def reconcile (first last : Fields α) : Option (List (Atom α)) :=
  if checkSameLabels first last then some (checks first last) else none

/-- The independently stated compatibility keeps both old self checks and
both new cross checks. Original fields, source names and rows are unchanged. -/
theorem reconcile_exact (assignment : α → Comp Common.model) (first last : Fields α) :
    (∃ atoms, reconcile first last = some atoms ∧ All Common.model assignment atoms) ↔
      SameLabels first last ∧ Compatible assignment first last := by
  by_cases accepted : checkSameLabels first last = true
  · have shape := (CommonRoleClosedRecordComparison.check_same_labels_exact first last).mp accepted
    constructor
    · rintro ⟨atoms, returned, models⟩
      have same : checks first last = atoms := by simpa [reconcile, accepted] using returned
      subst atoms
      exact ⟨shape, (checks_exact assignment first last shape).mp models⟩
    · rintro ⟨_, compatible⟩
      exact ⟨checks first last, by simp [reconcile, accepted],
        (checks_exact assignment first last shape).mpr compatible⟩
  · have different : ¬ SameLabels first last := fun shape =>
      accepted ((CommonRoleClosedRecordComparison.check_same_labels_exact first last).mpr shape)
    simp [reconcile, accepted, different]

end Yulang.CommonRoleClosedIntervalInspection
