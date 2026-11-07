import Yulang.PresenceRegularObservations

/-!
# Finite outer field observations cannot express exact emptiness

Every existing presence layer inspects only finitely many outer field names.
Adding a field beyond that finite support preserves its meaning, for arbitrary
payload predicates and masks. Consequently neither a layer nor all finite
observations of a regular root can denote the singleton empty record.

This is an expressiveness boundary of the existing `PresenceLayers.Layer`,
not an impossibility result for a richer presence model. In particular a
separate exact/closed-record constructor can remove this boundary without
changing the legacy width-supertype `records`.
-/

namespace Yulang.PresenceLayerExpressiveness

open PresenceLayers (Layer)
open PresenceDataTypes
open SourceDataRuntime

universe u
variable {State : Type u}

/-- A strict upper bound on the outer labels that a finite layer inspects.
Pair/variant payloads do not inspect their enclosing record's fields. -/
def labelBound : Layer State → Nat
  | .union left right | .inter left right => max (labelBound left) (labelBound right)
  | .required label _ | .optional label _ | .lacks label => label + 1
  | _ => 0

/-- The same fresh label works for every payload interpretation and mask. -/
theorem meaning_fresh_insert (assignment : State → Ty) (hidden : List Nat)
    (layer : Layer State) :
    ∀ (label : Nat) (payload : Value) (fields : List (Nat × Value)),
      labelBound layer ≤ label →
      (layer.meaning assignment hidden (.record (Fields.insert label payload fields)) ↔
        layer.meaning assignment hidden (.record fields)) := by
  induction layer with
  | union left right ihl ihr =>
      intro label payload fields fresh
      exact or_congr
        (ihl label payload fields (Nat.le_trans (Nat.le_max_left _ _) fresh))
        (ihr label payload fields (Nat.le_trans (Nat.le_max_right _ _) fresh))
  | inter left right ihl ihr =>
      intro label payload fields fresh
      exact and_congr
        (ihl label payload fields (Nat.le_trans (Nat.le_max_left _ _) fresh))
        (ihr label payload fields (Nat.le_trans (Nat.le_max_right _ _) fresh))
  | required name child =>
      intro label payload fields fresh
      have different : name ≠ label := by simp only [labelBound] at fresh; omega
      by_cases masked : name ∈ hidden <;> simp [Layer.meaning, masked, required, records, lookup,
        Fields.lookup_insert_other label name payload different fields]
  | optional name child =>
      intro label payload fields fresh
      have different : name ≠ label := by simp only [labelBound] at fresh; omega
      by_cases masked : name ∈ hidden <;> simp [Layer.meaning, masked, PresenceDataTypes.optional, records, lookup,
        Fields.lookup_insert_other label name payload different fields]
  | lacks name =>
      intro label payload fields fresh
      have different : name ≠ label := by simp only [labelBound] at fresh; omega
      by_cases masked : name ∈ hidden <;> simp [Layer.meaning, masked, lacks, records, lookup,
        Fields.lookup_insert_other label name payload different fields]
  | _ => intro label payload fields _; simp [Layer.meaning, base, exact, pair, variant, records, never, any]

/-- No finite layer represents exact emptiness, even if its child predicates
are arbitrary or encode complete regular/function type interpretations. -/
theorem no_exactEmpty_layer (assignment : State → Ty) (hidden : List Nat)
    (layer : Layer State) :
    ¬ (∀ value, layer.meaning assignment hidden value ↔ exactEmpty value) := by
  intro exactLayer
  have empty := (exactLayer (.record [])).mpr rfl
  have extra := (meaning_fresh_insert assignment hidden layer (labelBound layer)
    (.base .int) [] (Nat.le_refl _)).mpr empty
  have impossible := (exactLayer _).mp extra
  change Value.record [(labelBound layer, .base .int)] = Value.record [] at impossible
  cases impossible

/-- The finite support is independent of observation depth, so passing to
all depths does not manufacture the missing exact-record information. -/
theorem no_exactEmpty_all_observations (graph : PresenceRegularObservations.Graph State)
    (layer : Layer State) (hidden : List Nat) :
    ¬ (∀ value,
      (∀ depth, layer.meaning (PresenceRegularObservations.observe graph depth) hidden value) ↔
        exactEmpty value) := by
  intro exactLayer
  have empty := (exactLayer (.record [])).mpr rfl
  have extra : ∀ depth, layer.meaning (PresenceRegularObservations.observe graph depth)
      hidden (.record [(labelBound layer, .base .int)]) := by
    intro depth
    exact (meaning_fresh_insert _ hidden layer (labelBound layer) (.base .int) []
      (Nat.le_refl _)).mpr (empty depth)
  have impossible := (exactLayer _).mp extra
  change Value.record [(labelBound layer, .base .int)] = Value.record [] at impossible
  cases impossible

/-- The same obstruction holds for the union of finite observations, the
other natural interpretation of the existing bottom-based approximants. -/
theorem no_exactEmpty_some_observation (graph : PresenceRegularObservations.Graph State)
    (layer : Layer State) (hidden : List Nat) :
    ¬ (∀ value,
      (∃ depth, layer.meaning (PresenceRegularObservations.observe graph depth) hidden value) ↔
        exactEmpty value) := by
  intro exactLayer
  obtain ⟨depth, empty⟩ := (exactLayer (.record [])).mpr rfl
  have extra := (meaning_fresh_insert _ hidden layer (labelBound layer) (.base .int) []
    (Nat.le_refl _)).mpr empty
  have impossible := (exactLayer _).mp ⟨depth, extra⟩
  change Value.record [(labelBound layer, .base .int)] = Value.record [] at impossible
  cases impossible

end Yulang.PresenceLayerExpressiveness
