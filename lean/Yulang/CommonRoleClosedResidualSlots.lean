import Yulang.CommonRoleClosedResidualInspection
import Yulang.CommonDeclaredNominalSlots

/-!
# Canonical record remainder checks on original shared endpoint slots

Only the endpoints are specialized to original variable references. Their
assignments remain arbitrary Common types, including regular types. The
record spine and subtraction are computed by the existing canonical capture,
and every generated atom belongs to the existing complete worklist grammar.
-/

namespace Yulang.CommonRoleClosedResidualSlots

open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleCanonicalRows (Row lookup capture)
open CommonRoleIntervalRecordResidual (mapPayload lowerFields upperFields)
open CommonRoleClosedIntervalInspection (lookup_map same_labels_map)
open CommonRoleClosedRecordInspection (payloadChecks)
open CommonDeclaredNominalSlots (SlotAtom AllSlots)

abbrev Fields (α : Type) := Row (α × α)

def terms (fields : Fields α) : CommonRoleIntervalRecordResidual.Fields α :=
  mapPayload (fun bounds => (TyTerm.var bounds.1, TyTerm.var bounds.2)) fields

private theorem lower_terms (fields : Fields α) :
    lowerFields (terms fields) = mapPayload TyTerm.var (mapPayload Prod.fst fields) := by
  simp [lowerFields, terms, mapPayload, List.map_map]

private theorem upper_terms (fields : Fields α) :
    upperFields (terms fields) = mapPayload TyTerm.var (mapPayload Prod.snd fields) := by
  simp [upperFields, terms, mapPayload, List.map_map]

theorem payload_checks_slots (first last : Row α) :
    AllSlots (payloadChecks (mapPayload TyTerm.var first) (mapPayload TyTerm.var last)) := by
  intro atom member
  obtain ⟨entry, _, returned⟩ := List.mem_filterMap.mp member
  simp only [lookup_map] at returned
  cases sourceAt : lookup entry.1 first with
  | none => simp [sourceAt] at returned
  | some source =>
      cases targetAt : lookup entry.1 last with
      | none => simp [sourceAt, targetAt] at returned
      | some target =>
          have same : Atom.tyLe (.var source) (.var target) = atom := by
            simpa [sourceAt, targetAt] using returned
          subst atom
          exact SlotAtom.value source target

theorem checks_slots (first last : Fields α) :
    AllSlots (CommonRoleClosedIntervalInspection.checks (terms first) (terms last)) := by
  simp only [CommonRoleClosedIntervalInspection.checks, lower_terms, upper_terms]
  exact (payload_checks_slots _ _).append
    ((payload_checks_slots _ _).append
      ((payload_checks_slots _ _).append (payload_checks_slots _ _)))

structure Comparison (α : Type) where
  labels : List Nat
  fields : Fields α
  requested : Fields α

def inspect (comparison : Comparison α) : Option (List (Atom α)) :=
  CommonRoleClosedResidualInspection.inspect comparison.labels
    (terms comparison.fields) (terms comparison.requested)

def Compatible (assignment : α → Comp Common.model) (comparison : Comparison α) : Prop :=
  CommonRoleClosedRecordComparison.SameLabels
      (capture comparison.labels comparison.fields) comparison.requested ∧
    CommonRoleClosedIntervalRecordGeneration.Compatible assignment comparison.labels
      (terms comparison.fields) (CommonRoleClosedResidualInspection.argument (terms comparison.requested))

theorem inspect_exact (comparison : Comparison α) (assignment : α → Comp Common.model) :
    CommonNominalConstraints.Satisfied assignment (inspect comparison) ↔ Compatible assignment comparison := by
  rw [CommonNominalConstraints.Satisfied, inspect, CommonRoleClosedResidualInspection.inspect_exact]
  unfold Compatible
  rw [terms, CommonRoleIntervalRecordResidual.capture_map]
  exact and_congr (same_labels_map _ _ _ _) Iff.rfl

theorem inspect_slots (comparison : Comparison α) (atoms : List (Atom α))
    (returned : inspect comparison = some atoms) : AllSlots atoms := by
  unfold inspect CommonRoleClosedResidualInspection.inspect
    CommonRoleClosedIntervalInspection.reconcile at returned
  split at returned
  · have same := Option.some.inj returned
    subst atoms
    have captured : capture comparison.labels (terms comparison.fields) =
        terms (capture comparison.labels comparison.fields) :=
      CommonRoleIntervalRecordResidual.capture_map comparison.labels _ comparison.fields
    rw [captured]
    exact checks_slots _ _
  · contradiction

def inspectAll : List (Comparison α) → Option (List (Atom α))
  | [] => some []
  | comparison :: rest => CommonNominalConstraints.append (inspect comparison) (inspectAll rest)

def Models (comparisons : List (Comparison α)) (assignment : α → Comp Common.model) : Prop :=
  ∀ comparison ∈ comparisons, Compatible assignment comparison

theorem inspect_all_exact (comparisons : List (Comparison α)) (assignment : α → Comp Common.model) :
    CommonNominalConstraints.Satisfied assignment (inspectAll comparisons) ↔ Models comparisons assignment := by
  induction comparisons with
  | nil => simp [inspectAll, Models, PresenceNormalForm.All]
  | cons comparison rest ih =>
      simp only [inspectAll, CommonNominalConstraints.append_exact, inspect_exact, ih, Models,
        List.mem_cons, forall_eq_or_imp]

theorem inspect_all_slots (comparisons : List (Comparison α)) (atoms : List (Atom α))
    (returned : inspectAll comparisons = some atoms) : AllSlots atoms := by
  induction comparisons generalizing atoms with
  | nil => simp [inspectAll] at returned; subst atoms; simp [AllSlots]
  | cons comparison rest ih =>
      cases first : inspect comparison with
      | none => simp [inspectAll, first, CommonNominalConstraints.append] at returned
      | some added =>
          cases last : inspectAll rest with
          | none => simp [inspectAll, first, last, CommonNominalConstraints.append] at returned
          | some remaining =>
              have same : added ++ remaining = atoms := by
                simpa [inspectAll, first, last, CommonNominalConstraints.append] using returned
              subst atoms
              exact (inspect_slots comparison added first).append (ih remaining last)

/-- All three hypotheses required for completeness of the ordinary Common
worklist are derived from the actual generated list, without restricting any
assignment of the original endpoints. -/
theorem inspect_all_grammar (comparisons : List (Comparison α)) (atoms : List (Atom α))
    (returned : inspectAll comparisons = some atoms) :
    PresenceGeneratedChildGrammar.GoodAtoms atoms ∧
      PresenceGeneratedWidth.WidthAtoms atoms ∧
      PresenceSourceConstraintSupport.GoodAtoms atoms := by
  have slots := inspect_all_slots comparisons atoms returned
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    cases slots atom member <;> trivial
  · intro source target member tail required
    cases slots (.tyLe source target) member
    cases required
  · intro atom member
    cases slots atom member <;> trivial

end Yulang.CommonRoleClosedResidualSlots
