import Yulang.ShadowSemanticRecords
import Yulang.RigidRecordFields

/-!
# Exact rigid demands for records with arbitrary-tail shadowing

The decision-40 relation has the same masked decomposition of a rigid
record demand as decision 39. The field comparisons below use the extended
relation throughout; they are not restricted to old subtype derivations.

The supply, its field values, and its tail are arbitrary raw types. Only the
demand has to be a proper record spine. No row laws, record distribution,
or covariance into an arbitrary tail are assumed.
-/

namespace Yulang.ShadowRecordDemands

open StructuralBase (Ty IsRecord)
open ShadowSemanticRecords (Subtype)
open RigidRecordFields (erase erase_record lookup_erase)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

/-- Comparison against a rigid demand, recursively inspecting only the
supply. Nested field comparisons use the full decision-40 relation. -/
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

/-- On a proper supply the recursive demands are exactly first-field
lookup obligations, with shadowed payloads absent from those obligations. -/
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

/-- The new shadow equation preserves every demand, including arbitrary
raw demands. After the first field, the repeated label has no lookup
obligation, and erasing it again leaves the residual demand unchanged. -/
theorem fits_shadow (label : Nat) (visible hidden rest target : Ty Row) :
    Fits leRow (.record label visible (.record label hidden rest)) target ↔
      Fits leRow (.record label visible rest) target := by
  simp [Fits]

/-- Every rule of the extended relation preserves all masked observations.
In particular, both directions of arbitrary-tail shadowing are handled
directly, without reducing field premises to the preceding relation. -/
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
  | shadowErase label visible hidden rest =>
      exact fun target fits => (fits_shadow label visible hidden rest target).mpr fits
  | shadowInsert label visible hidden rest =>
      exact fun target fits => (fits_shadow label visible hidden rest target).mp fits

/-- A supplied head discharges its own visible obligation. The supplied
tail need only meet the remaining rigid demand; no hidden payload is
compared against the demanded head type. -/
theorem record_mask_sufficient (label : Nat) (value : Ty Row) {rest target : Ty Row}
    (rigid : IsRecord target) (tail : Subtype leRow rest (erase label target))
    (head : ∀ expected, target.lookup label = some expected → Subtype leRow value expected) :
    Subtype leRow (.record label value rest) target := by
  refine .trans (.recordTail (erase_record label rigid) tail) ?_
  apply Subtype.record (.field (erase_record label rigid)) rigid
  · intro key expected found
    by_cases same : key = label
    · exact ⟨value, by simp [Ty.lookup, same]⟩
    · exact ⟨expected, by simpa [Ty.lookup, same] using found⟩
  · intro key actual expected actualFound expectedFound
    by_cases same : key = label
    · subst key
      have equal : value = actual := by simpa [Ty.lookup] using actualFound
      subst actual
      exact head expected expectedFound
    · have equal : actual = expected := by
        have found : target.lookup key = some actual := by simpa [Ty.lookup, same] using actualFound
        simpa [expectedFound] using found.symm
      subst expected
      exact .refl _

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
      exact record_mask_sufficient label value rigid
        (tail (erase_record label rigid) fits.2) fits.1

/-- Exact comparison for every raw supply and every rigid demand, with
no row-algebra or decidability assumptions. -/
theorem subtype_iff_fits (source : Ty Row) {target : Ty Row} (rigid : IsRecord target) :
    Subtype leRow source target ↔ Fits leRow source target :=
  ⟨fun below => fits_contravariant below target (proper_fits_self rigid), fits_sound rigid⟩

/-- The head and masked tail obligations are both necessary and sufficient
in the full decision-40 relation. The tail and all payloads are unrestricted. -/
theorem record_mask_exact (label : Nat) (value rest : Ty Row) {target : Ty Row}
    (rigid : IsRecord target) :
    Subtype leRow (.record label value rest) target ↔
      (∀ expected, target.lookup label = some expected → Subtype leRow value expected) ∧
        Subtype leRow rest (erase label target) := by
  rw [subtype_iff_fits _ rigid]
  change _ ∧ Fits leRow rest (erase label target) ↔ _
  rw [← subtype_iff_fits rest (erase_record label rigid)]

/-- An empty demand imposes only the residual tail obligation. Even here,
an arbitrary supplied tail is not silently accepted as a record. -/
theorem record_empty_exact (label : Nat) (value rest : Ty Row) :
    Subtype leRow (.record label value rest) .emptyRecord ↔
      Subtype leRow rest .emptyRecord := by
  simpa [Ty.lookup, erase] using
    record_mask_exact (leRow := leRow) label value rest (target := .emptyRecord) .empty

/-- A matching singleton demand compares the visible payload and requires
only an empty record demand of the arbitrary supplied tail. -/
theorem record_singleton_same_exact (label : Nat) (value rest expected : Ty Row) :
    Subtype leRow (.record label value rest) (.record label expected .emptyRecord) ↔
      Subtype leRow value expected ∧ Subtype leRow rest .emptyRecord := by
  simpa [Ty.lookup, erase] using
    record_mask_exact (leRow := leRow) label value rest
      (target := .record label expected .emptyRecord) (.field .empty)

/-- A different supplied head leaves the singleton demand unchanged and
imposes no constraint on the supplied head's payload. -/
theorem record_singleton_other_exact (label demanded : Nat)
    (different : label ≠ demanded) (value rest expected : Ty Row) :
    Subtype leRow (.record label value rest) (.record demanded expected .emptyRecord) ↔
      Subtype leRow rest (.record demanded expected .emptyRecord) := by
  simpa [Ty.lookup, erase, different] using
    record_mask_exact (leRow := leRow) label value rest
      (target := .record demanded expected .emptyRecord) (.field .empty)

end Yulang.ShadowRecordDemands
