import Yulang.CommonNominalDefaultRequired
import Yulang.CommonNominalRecord

/-!
# Whole-default inspection against a record with the same head

The head contributes the shifted optional-payload obligation and the finite
presence/fallback choice. All other required fields and nontrivial optional
tests pass directly to the source at the same constructor depth. The updated
field, record-kind demands and trivial optional tests are not passed back.
-/

namespace Yulang.CommonNominalDefaultRequired

universe u

/-- The finite selected-head comparison and independent remaining-source
comparison account for every observation of the record target. -/
theorem finite_default_record_split {Row : Type u} (leRow : Row → Row → Prop)
    (label : Nat) (source fallback payload tail : CommonNominalFinite.Ty Row) :
    CommonNominalFinite.ProducerLe leRow (.recordDefault label source fallback) (.record label payload tail) ↔
      CommonNominalFinite.ProducerLe leRow (.recordDefault label source fallback)
        (CommonNominalFinite.required label payload) ∧
      CommonNominalFinite.RecordTailLe leRow [label] source tail := by
  constructor
  · intro below
    constructor
    · apply CommonNominalFinite.producerLe_trans below
      exact (CommonNominalFinite.producerLe_record_iff label payload payload tail .emptyRecord).mpr
        ⟨CommonNominalFinite.producerLe_refl _, CommonNominalFinite.recordTailLe_emptyRecord [label] tail⟩
    · constructor
      · intro rank env current visible obs accepted
        have different : current ≠ label := by simpa using visible
        have target : CommonNominalFinite.ProbeAt leRow rank env (.record label payload tail)
            (.field current obs) := by
          simpa only [CommonNominalFinite.probeAt_record_field, different, ↓reduceIte] using accepted
        have output := (CommonNominalFinite.producerLe_iff_probe _ _).mp below rank env _ target
        simpa only [CommonNominalFinite.probeAt_default_field, different, ↓reduceIte] using output
      · intro rank env current visible obs nontrivial accepted
        have different : current ≠ label := by simpa using visible
        have target : CommonNominalFinite.ProbeAt leRow rank env (.record label payload tail)
            (.optional current obs) := by
          simpa only [CommonNominalFinite.probeAt_record_optional, different, ↓reduceIte,
            nontrivial, or_false] using accepted
        have output := (CommonNominalFinite.producerLe_iff_probe _ _).mp below rank env _ target
        simpa only [CommonNominalFinite.probeAt_default_optional, different, ↓reduceIte,
          nontrivial, or_false] using output
  · rintro ⟨selected, fields, optional⟩
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    cases obs with
    | field current inner =>
        by_cases same : current = label
        · subst current
          apply (CommonNominalFinite.producerLe_iff_probe _ _).mp selected rank env (.field label inner)
          simpa only [CommonNominalFinite.required, CommonNominalFinite.probeAt_record_field, ↓reduceIte] using accepted
        · simp only [CommonNominalFinite.probeAt_record_field, same, ↓reduceIte] at accepted
          simpa only [CommonNominalFinite.probeAt_default_field, same, ↓reduceIte] using
            fields rank env current (by simpa using same) inner accepted
    | optional current inner =>
        by_cases same : current = label
        · subst current
          apply (CommonNominalFinite.producerLe_iff_probe _ _).mp selected rank env (.optional label inner)
          simpa only [CommonNominalFinite.required, CommonNominalFinite.probeAt_record_optional, ↓reduceIte] using accepted
        · simp only [CommonNominalFinite.probeAt_record_optional, same, ↓reduceIte] at accepted
          rw [CommonNominalFinite.probeAt_default_optional]
          simp only [same, ↓reduceIte]
          by_cases trivial : inner = .trivial
          · exact Or.inr trivial
          · exact Or.inl (optional rank env current (by simpa using same) inner trivial
              (accepted.resolve_right trivial))
    | _ => cases rank <;> exact accepted

/-- The same-depth tail comparison includes depth zero, where a common
default has the ordinary record constructor with a bottom head payload. -/
theorem default_record_split (label : Nat) (source fallback payload tail : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.record label payload tail) ↔
      CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.required label payload) ∧
        CommonNominalCarrier.RecordTailLe [label] source tail := by
  constructor
  · intro below
    constructor
    · intro depth
      apply CommonNominalFinite.producerLe_trans (below depth)
      exact (CommonNominalFinite.producerLe_record_iff label _ _ _ .emptyRecord).mpr
        ⟨CommonNominalFinite.producerLe_refl _, CommonNominalFinite.recordTailLe_emptyRecord [label] _⟩
    · intro depth
      cases depth with
      | zero => exact ((CommonNominalFinite.producerLe_record_iff label _ _ _ _).mp (below 0)).2
      | succ depth => exact ((finite_default_record_split Common.rowLe label _ _ _ _).mp
          (below (depth + 1))).2
  · rintro ⟨selected, remaining⟩ depth
    cases depth with
    | zero =>
        exact (CommonNominalFinite.producerLe_record_iff label _ _ _ _).mpr
          ⟨CommonNominalFinite.producerLe_refl _, remaining 0⟩
    | succ depth =>
        exact (finite_default_record_split Common.rowLe label _ _ _ _).mpr
          ⟨selected (depth + 1), remaining (depth + 1)⟩

/-- Exact selected-head record-target rule. The output obligations contain
only independent optional source information, a finite source presence test
or proper fallback comparison, and the unmodified remaining-source demands. -/
theorem default_record_iff (label : Nat) (source fallback payload tail : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.record label payload tail) ↔
      OptionalPayload label source payload ∧
        (present label source = true ∨ CommonNominalCarrier.model.subTy fallback payload) ∧
        CommonNominalCarrier.RecordTailLe [label] source tail := by
  rw [default_record_split, default_required_iff, and_assoc]

end Yulang.CommonNominalDefaultRequired
