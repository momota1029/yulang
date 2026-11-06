import Yulang.RigidRecordFields

/-!
# Exact visible-field demands on arbitrary supplied record tails

The demanded type is a rigid spine. Its same-labelled fields are erased
after a supplied head has been checked, so hidden payloads are never compared.
The supply may contain arbitrary lattice expressions and open record tails.

No record distribution or general tail covariance is used. In particular,
intersection supplies satisfy a rigid demand through one branch, as required
by the existing free-lattice subtype relation.
-/

namespace Yulang.RigidRecordDemands

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype)
open RigidRecordFields (erase erase_record lookup_erase)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

/-- A structural description of comparison to a rigid demand. Recursion is
only on the supply; nested field values keep the original subtype relation. -/
def Fits (leRow : Row → Row → Prop) : Ty Row → Ty Row → Prop
  | .bottom, _ => True
  | .top, _ => False
  | .union left right, target => Fits leRow left target ∧ Fits leRow right target
  | .inter left right, target => Fits leRow left target ∨ Fits leRow right target
  | .emptyRecord, target => ∀ label expected, target.lookup label = some expected → False
  | .record label value rest, target =>
      (∀ expected, target.lookup label = some expected → Subtype leRow value expected) ∧
        Fits leRow rest (erase label target)
  | _, _ => False

/-- On a proper supply the recursive demands are exactly first-field lookup
obligations, even when hidden fields have different payload types. -/
theorem proper_fits_iff {source : Ty Row} (shape : IsRecord source) (target : Ty Row) :
    Fits leRow source target ↔
      ∀ label expected, target.lookup label = some expected →
        ∃ actual, source.lookup label = some actual ∧ Subtype leRow actual expected := by
  induction shape generalizing target with
  | empty =>
      constructor
      · intro fits label expected found
        exact False.elim (fits label expected found)
      · intro fields label expected found
        obtain ⟨actual, impossible, _⟩ := fields label expected found
        cases impossible
  | @field rest name value _ ih =>
      change ((∀ expected, target.lookup name = some expected → Subtype leRow value expected) ∧
        Fits leRow rest (erase name target)) ↔ _
      rw [ih]
      constructor
      · rintro ⟨head, tail⟩ label expected found
        by_cases same : label = name
        · subst label
          exact ⟨value, by simp [Ty.lookup], head expected found⟩
        · obtain ⟨actual, actualFound, below⟩ := tail label expected (by simpa [same] using found)
          exact ⟨actual, by simpa [Ty.lookup, same] using actualFound, below⟩
      · intro fields
        constructor
        · intro expected found
          obtain ⟨actual, actualFound, below⟩ := fields name expected found
          have equal : value = actual := by simpa [Ty.lookup] using actualFound
          simpa [equal] using below
        · intro label expected found
          have distinct : label ≠ name := by
            intro same
            subst label
            simp at found
          obtain ⟨actual, actualFound, below⟩ := fields label expected (by simpa [distinct] using found)
          exact ⟨actual, by simpa [Ty.lookup, distinct] using actualFound, below⟩

theorem proper_fits_self {type : Ty Row} (shape : IsRecord type) : Fits leRow type type :=
  (proper_fits_iff shape type).mpr (fun _ expected found => ⟨expected, found, .refl _⟩)

/-- Every declarative rule preserves all rigid observations. Keeping the
demand arbitrary in this lemma makes the shadowing induction explicit. -/
theorem fits_contravariant {a b : Ty Row} (below : Subtype leRow a b) :
    ∀ target, Fits leRow b target → Fits leRow a target := by
  induction below with
  | refl => exact fun _ fits => fits
  | trans _ _ first last => exact fun target fits => first target (last target fits)
  | bottom => exact fun _ _ => trivial
  | top => exact fun _ impossible => False.elim impossible
  | unionLeft => exact fun _ fits => fits.1
  | unionRight => exact fun _ fits => fits.2
  | unionElim _ _ first last => exact fun target fits => ⟨first target fits, last target fits⟩
  | interLeft => exact fun _ fits => Or.inl fits
  | interRight => exact fun _ fits => Or.inr fits
  | interIntro _ _ first last => exact fun target fits => fits.elim (first target) (last target)
  | pair | variant | arrow => exact fun _ impossible => False.elim impossible
  | @record source target sourceShape targetShape coverage values _ =>
      intro demand fits
      apply (proper_fits_iff sourceShape demand).mpr
      intro label expected found
      obtain ⟨middle, middleFound, last⟩ := (proper_fits_iff targetShape demand).mp fits label expected found
      obtain ⟨actual, actualFound⟩ := coverage label middle middleFound
      exact ⟨actual, actualFound, .trans (values label actual middle actualFound middleFound) last⟩
  | @recordCongr value value' rest rest' label head _ _ _ _ _ tail _ =>
      intro target fits
      exact ⟨fun expected found => .trans head (fits.1 expected found), tail _ fits.2⟩
  | recordTail _ _ tail =>
      intro target fits
      exact ⟨fits.1, tail _ fits.2⟩

theorem fits_sound {source target : Ty Row} (rigid : IsRecord target)
    (fits : Fits leRow source target) : Subtype leRow source target := by
  induction source generalizing target with
  | bottom => exact .bottom _
  | top | base | pair | variant | arrow => cases fits
  | union left right first last => exact .unionElim (first rigid fits.1) (last rigid fits.2)
  | inter left right first last =>
      rcases fits with fits | fits
      · exact .trans (.interLeft left right) (first rigid fits)
      · exact .trans (.interRight left right) (last rigid fits)
  | emptyRecord =>
      apply Subtype.record .empty rigid
      · intro label expected found
        exact False.elim (fits label expected found)
      · intro label actual expected actualFound _
        cases actualFound
  | record label value rest _ tail =>
      exact RigidRecordFields.record_mask_sufficient label value rigid
        (tail (erase_record label rigid) fits.2) fits.1

/-- Complete masked comparison for every raw supply and every rigid demand.
There are no row-algebra or decidability assumptions. -/
theorem subtype_iff_fits (source : Ty Row) {target : Ty Row} (rigid : IsRecord target) :
    Subtype leRow source target ↔ Fits leRow source target :=
  ⟨fun below => fits_contravariant below target (proper_fits_self rigid), fits_sound rigid⟩

/-- The tail is tested only against the demanded fields not shadowed by the
new head. This is an iff, not merely a sound sufficient condition. -/
theorem record_mask_exact (label : Nat) (value rest : Ty Row) {target : Ty Row}
    (rigid : IsRecord target) :
    Subtype leRow (.record label value rest) target ↔
      (∀ expected, target.lookup label = some expected → Subtype leRow value expected) ∧
        Subtype leRow rest (erase label target) := by
  rw [subtype_iff_fits _ rigid]
  change _ ∧ Fits leRow rest (erase label target) ↔ _
  rw [← subtype_iff_fits rest (erase_record label rigid)]

end Yulang.RigidRecordDemands
