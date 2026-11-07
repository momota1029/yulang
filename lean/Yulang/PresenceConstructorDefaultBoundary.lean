import Yulang.PresenceDataTypes
import Yulang.ProducerRanked

/-!
# Strict whole default images and structural producer observations

`PresenceDataTypes.recordDefault` is the image of two already evaluated
operands. It therefore has no result if either operand supplies no value,
even when the source already contains the field being defaulted. The exact
present-source identity below names the necessary and sufficient hypothesis:
the fallback predicate must have an inhabitant.

The ranked demand model, separately, keeps the shape of a pair with a bottom
payload. These are facts about the existing two models, not new language
equations. In particular `spec/10-inference-core.md` 10.28 does not add
constructor bottom-strictness. A common presence model must state and prove
its chosen producer-image and demand-observation laws instead of silently
identifying these interpretations.
-/

namespace Yulang.PresenceConstructorDefaultBoundary

open PresenceDataTypes
open SourceDataRuntime

theorem recordDefault_never_fallback (label : Nat) (source : Ty) :
    recordDefault label source never = never := by
  funext result
  apply propext
  simp [recordDefault, never]

theorem recordDefault_never_source (label : Nat) (fallback : Ty) :
    recordDefault label never fallback = never := by
  funext result
  apply propext
  simp [recordDefault, never]

/-- Exact whole-image inhabitation, for arbitrary operand predicates and all
labels. Non-record source values cannot be used as default-extension bases. -/
theorem recordDefault_inhabited_iff (label : Nat) (source fallback : Ty) :
    (∃ result, recordDefault label source fallback result) ↔
      (∃ fields, source (.record fields)) ∧ ∃ value, fallback value := by
  constructor
  · rintro ⟨_, fields, value, sourceValid, fallbackValid, _⟩
    exact ⟨⟨fields, sourceValid⟩, ⟨value, fallbackValid⟩⟩
  · rintro ⟨⟨fields, sourceValid⟩, ⟨value, fallbackValid⟩⟩
    exact ⟨.record (Fields.insertDefault label value fields),
      fields, value, sourceValid, fallbackValid, rfl⟩

/-- A known-present source is returned unchanged as a whole record image
exactly when the strictly evaluated fallback has some value. All unrelated
fields and their payloads remain in the exact source record. -/
theorem present_exact_image_iff (label : Nat) (fields : List (Nat × Value))
    (existing : Value) (present : Fields.lookup label fields = some existing) (fallback : Ty) :
    recordDefault label (exact (.record fields)) fallback = exact (.record fields) ↔
      ∃ value, fallback value := by
  constructor
  · intro same
    have valid : recordDefault label (exact (.record fields)) fallback (.record fields) :=
      same.symm ▸ (rfl : exact (.record fields) (.record fields))
    obtain ⟨_, value, _, valid, _⟩ := valid
    exact ⟨value, valid⟩
  · rintro ⟨fallbackValue, fallbackValid⟩
    funext result
    apply propext
    constructor
    · rintro ⟨actualFields, value, sourceValid, _, resultEq⟩
      have fieldsEq : actualFields = fields := Value.record.inj sourceValid
      subst actualFields
      change result = .record fields
      simpa only [Fields.insertDefault_present label value existing fields present] using resultEq
    · intro same
      exact ⟨fields, fallbackValue, rfl, fallbackValid,
        same.trans (congrArg Value.record
          (Fields.insertDefault_present label fallbackValue existing fields present).symm)⟩

namespace PresentSource

def source : Value := .record [(7, .base .int)]
def sourceType : Ty := exact source

theorem known_present : required 7 (base .int) source := by
  exact ⟨trivial, .base .int, rfl, rfl⟩

/-- Field selection would keep the integer, but the whole strict image is
empty because the fallback operand produces no value. -/
theorem empty_fallback_image : recordDefault 7 sourceType never = never :=
  recordDefault_never_fallback 7 sourceType

theorem no_default_result : ¬ ∃ result, recordDefault 7 sourceType never result := by
  rw [empty_fallback_image]
  exact fun ⟨_, impossible⟩ => impossible

/-- The exact present source itself is not contained in the whole image;
known presence alone cannot justify discarding the fallback operand. -/
theorem present_source_not_preserved : ¬ Le sourceType (recordDefault 7 sourceType never) := by
  rw [empty_fallback_image]
  exact fun below => below source rfl

theorem present_image_not_source : recordDefault 7 sourceType never ≠ sourceType := by
  intro same
  exact present_source_not_preserved (same.symm ▸ le_refl sourceType)

end PresentSource

/-- In the ranked demand model, a constructed pair retains its shape even
with a bottom component. This theorem has no assumptions on the row relation. -/
theorem pair_bottom_not_below_bottom {Row : Type u} (leRow : Row → Row → Prop)
    (other : StructuralBase.Ty Row) :
    ¬ ProducerRanked.ProducerLe leRow (.pair .bottom other) .bottom := by
  intro below
  exact (ProducerRanked.producerLe_iff_probe _ _).mp below 0 .impossible
    (ProducerRanked.probeAt_bottom 0 .impossible)

theorem pair_bottom_not_equivalent_bottom {Row : Type u} (leRow : Row → Row → Prop)
    (other : StructuralBase.Ty Row) :
    ¬ ProducerRanked.ProducerEq leRow (.pair .bottom other) .bottom :=
  fun same => pair_bottom_not_below_bottom leRow other same.1

end Yulang.PresenceConstructorDefaultBoundary
