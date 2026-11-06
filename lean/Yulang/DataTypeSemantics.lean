import Yulang.SourceDataRuntime
import Yulang.RigidSemanticRecords

/-!
# Finite data meanings of structural types

The hidden-label parameter records fields shadowed by an enclosing record
head. It is threaded through unions and intersections, so opaque tails retain
their meaning while an older duplicate field imposes no requirement.
This interpretation is sound for the decision-39 relation and already validates
the new decision-40 shadow equation, for arbitrary tails.

The values here are first-order data. Arrow types have no such values; this is
not a semantics of closures, recursive value types or effectful computations.
In particular no function-safety statement is inferred from an empty arrow
interpretation. The operational theorem using this module explicitly excludes
functions from its source fragment.
-/

namespace Yulang.DataTypeSemantics

open Inference
open StructuralBase (Ty IsRecord)
open SourceDataRuntime

universe u

abbrev Mask := Nat → Prop

def visible : Mask := fun _ => False

def hide (label : Nat) (mask : Mask) : Mask := fun query => query = label ∨ mask query

def Holds : Ty Row → Mask → Value → Prop
  | .bottom, _, _ => False
  | .top, _, _ => True
  | .base expected, _, .base actual => actual = expected
  | .base _, _, _ => False
  | .union left right, mask, value => Holds left mask value ∨ Holds right mask value
  | .inter left right, mask, value => Holds left mask value ∧ Holds right mask value
  | .pair left right, _, .pair first last => Holds left visible first ∧ Holds right visible last
  | .pair _ _, _, _ => False
  | .emptyRecord, _, .record _ => True
  | .emptyRecord, _, _ => False
  | .record label head tail, mask, .record fields =>
      (¬ mask label → ∃ value, Fields.lookup label fields = some value ∧ Holds head visible value) ∧
        Holds tail (hide label mask) (.record fields)
  | .record _ _ _, _, _ => False
  | .variant label payload, _, .variant tag value => tag = label ∧ Holds payload visible value
  | .variant _ _, _, _ => False
  | .arrow _ _ _ _, _, _ => False

/-- Masking additional fields can only forget record requirements. -/
theorem mask_mono (type : Ty Row) {first last : Mask}
    (includes : ∀ label, first label → last label) (value : Value)
    (valid : Holds type first value) : Holds type last value := by
  induction type generalizing first last value with
  | bottom => exact False.elim valid
  | top => trivial
  | base => cases value <;> exact valid
  | union left right ihl ihr =>
      exact valid.elim (fun h => Or.inl (ihl includes value h))
        (fun h => Or.inr (ihr includes value h))
  | inter left right ihl ihr =>
      exact ⟨ihl includes value valid.1, ihr includes value valid.2⟩
  | pair => cases value <;> exact valid
  | emptyRecord => cases value <;> exact valid
  | variant => cases value <;> exact valid
  | arrow => exact valid
  | record label head tail _ iht =>
      cases value with
      | base | pair | variant => exact False.elim valid
      | record fields =>
          refine ⟨fun notMasked => valid.1 (fun old => notMasked (includes _ old)), ?_⟩
          exact iht (fun query old => old.elim Or.inl (fun h => Or.inr (includes query h)))
            (.record fields) valid.2

theorem mask_congr (type : Ty Row) {first last : Mask}
    (same : ∀ label, first label ↔ last label) (value : Value) :
    Holds type first value ↔ Holds type last value :=
  ⟨mask_mono type (fun label h => (same label).mp h) value,
    mask_mono type (fun label h => (same label).mpr h) value⟩

/-- Changing stored fields hidden by the mask does not change the type meaning. -/
theorem record_agreement (type : Ty Row) (mask : Mask)
    (first last : List (Nat × Value))
    (agree : ∀ label, ¬ mask label → Fields.lookup label first = Fields.lookup label last) :
    Holds type mask (.record first) ↔ Holds type mask (.record last) := by
  induction type generalizing mask with
  | bottom | top | base | pair | emptyRecord | variant | arrow => rfl
  | union left right ihl ihr =>
      exact or_congr (ihl mask agree) (ihr mask agree)
  | inter left right ihl ihr =>
      exact and_congr (ihl mask agree) (ihr mask agree)
  | record label head tail _ iht =>
      apply and_congr
      · apply forall_congr'
        intro unmasked
        rw [agree label unmasked]
      · exact iht (hide label mask) (fun query unmasked =>
          agree query (fun old => unmasked (Or.inr old)))

theorem record_shape {type : Ty Row} (shape : IsRecord type)
    (mask : Mask) (value : Value) (valid : Holds type mask value) :
    ∃ fields, value = .record fields := by
  cases shape <;> cases value <;> simp_all [Holds]

/-- On rigid records the masked meaning is exactly first-field-wins lookup. -/
theorem rigid_record_iff {type : Ty Row} (shape : IsRecord type)
    (mask : Mask) (fields : List (Nat × Value)) :
    Holds type mask (.record fields) ↔
      ∀ label expected, type.lookup label = some expected → ¬ mask label →
        ∃ value, Fields.lookup label fields = some value ∧ Holds expected visible value := by
  induction shape generalizing mask with
  | empty => simp [Holds, Ty.lookup]
  | @field tail label head shape ih =>
      change ((_ → _) ∧ Holds tail (hide label mask) (.record fields)) ↔ _
      rw [ih]
      constructor
      · intro valid query expected found unmasked
        by_cases same : query = label
        · subst query
          have equal : head = expected := Option.some.inj (by simpa [Ty.lookup] using found)
          subst expected
          exact valid.1 unmasked
        · exact valid.2 query expected (by simpa [Ty.lookup, same] using found)
            (fun hidden => hidden.elim same unmasked)
      · intro valid
        refine ⟨fun unmasked => valid label head (by simp [Ty.lookup]) unmasked, ?_⟩
        intro query expected found unmasked
        have different : query ≠ label := fun equal => unmasked (Or.inl equal)
        exact valid query expected (by simpa [Ty.lookup, different] using found)
          (fun hidden => unmasked (Or.inr hidden))

/-- The actual insertion operation validates the record constructor; the tail
is observed with the overwritten coordinate hidden. -/
theorem record_intro (label : Nat) (head tail : Ty Row) (value : Value)
    (fields : List (Nat × Value))
    (headValid : Holds head visible value) (tailValid : Holds tail visible (.record fields)) :
    Holds (.record label head tail) visible (.record (Fields.insert label value fields)) := by
  refine ⟨fun _ => ⟨value, Fields.lookup_insert_same _ _ _, headValid⟩, ?_⟩
  apply (record_agreement tail (hide label visible) fields
    (Fields.insert label value fields) ?_).mp
  · exact mask_mono tail (fun _ impossible => False.elim impossible) _ tailValid
  · intro query unmasked
    exact (Fields.lookup_insert_other label query value
      (fun equal => unmasked (Or.inl equal)) fields).symm

/-- The new shadow equation is valid without a rigidity or admissibility
assumption on the opaque tail, or on the hidden payload type. -/
theorem record_shadow (label : Nat) (head hidden tail : Ty Row)
    (mask : Mask) (value : Value) :
    Holds (.record label head (.record label hidden tail)) mask value ↔
      Holds (.record label head tail) mask value := by
  cases value with
  | base | pair | variant => rfl
  | record fields =>
      change (_ ∧ ((_ → _) ∧ _)) ↔ (_ ∧ _)
      have duplicate : hide label (hide label mask) = hide label mask := by
        funext query
        apply propext
        simp [hide]
      simp only [duplicate]
      have hiddenHead : ¬ hide label mask label →
          ∃ item, Fields.lookup label fields = some item ∧ Holds hidden visible item :=
        fun impossible => False.elim (impossible (Or.inl rfl))
      exact ⟨fun valid => ⟨valid.1, valid.2.2⟩,
        fun valid => ⟨valid.1, hiddenHead, valid.2⟩⟩

def Preserves (relation : Ty Row → Ty Row → Prop) : Prop :=
  ∀ {source target}, relation source target →
    ∀ mask value, Holds source mask value → Holds target mask value

/-- Every declared decision-39 comparison preserves the independently defined
finite-data meaning, at every shadowing mask. -/
theorem rigid_subtype_preserves {leRow : Row → Row → Prop} :
    Preserves (RigidSemanticRecords.Subtype leRow) := by
  intro source target below
  induction below with
  | refl => exact fun _ _ valid => valid
  | trans _ _ first last => exact fun mask value valid => last mask value (first mask value valid)
  | bottom => exact fun _ _ impossible => False.elim impossible
  | top => exact fun _ _ _ => trivial
  | unionLeft => exact fun _ _ valid => Or.inl valid
  | unionRight => exact fun _ _ valid => Or.inr valid
  | unionElim _ _ first last =>
      exact fun mask value valid => valid.elim (first mask value) (last mask value)
  | interLeft => exact fun _ _ valid => valid.1
  | interRight => exact fun _ _ valid => valid.2
  | interIntro _ _ first last =>
      exact fun mask value valid => ⟨first mask value valid, last mask value valid⟩
  | pair _ _ first last =>
      intro mask value valid
      cases value with
      | pair a b => exact ⟨first visible a valid.1, last visible b valid.2⟩
      | base | record | variant => exact False.elim valid
  | variant _ payload =>
      intro mask value valid
      cases value with
      | variant label body => exact ⟨valid.1, payload visible body valid.2⟩
      | base | pair | record => exact False.elim valid
  | arrow => exact fun _ _ impossible => False.elim impossible
  | record sourceShape targetShape available _ payloads =>
      intro mask value valid
      obtain ⟨fields, rfl⟩ := record_shape sourceShape mask value valid
      apply (rigid_record_iff targetShape mask fields).mpr
      intro label expected found unmasked
      obtain ⟨actual, actualFound⟩ := available label expected found
      obtain ⟨item, itemFound, itemValid⟩ :=
        (rigid_record_iff sourceShape mask fields).mp valid label actual actualFound unmasked
      exact ⟨item, itemFound, payloads label actual expected actualFound found visible item itemValid⟩
  | recordCongr _ _ _ _ headForward _ tailForward _ =>
      intro mask value valid
      cases value with
      | record fields =>
          refine ⟨?_, tailForward _ _ valid.2⟩
          intro unmasked
          obtain ⟨item, found, good⟩ := valid.1 unmasked
          exact ⟨item, found, headForward visible item good⟩
      | base | pair | variant => exact False.elim valid
  | recordTail _ _ tail =>
      intro mask value valid
      cases value with
      | record fields => exact ⟨valid.1, tail _ _ valid.2⟩
      | base | pair | variant => exact False.elim valid

end Yulang.DataTypeSemantics
