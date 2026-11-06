import Yulang.CommonPayloadProjection
import Yulang.CommonRecordEnvelope

/-!
# Whole-default comparison with an arbitrary common target

The selected field and optional tests are finite payload projections. Their
comparison is an ordinary child subtype relation, or a Boolean failure when
the producer has no corresponding field. The outer head restriction is the
executable record-envelope guard. All remaining labels pass unchanged to the
proper source operand at the same constructor depth.

This decomposition contains no comparison whose left side is the original
whole default. The final record-tail relation is explicit; eliminating its
unbounded label quantifier is a separate finite inspection step.
-/

namespace Yulang.CommonDefaultTargetSplit

open CommonPayloadProjection

theorem fieldComparison_exact (label : Nat) (source target : Common.Ty) :
    ProfileLe (fieldType [] label source) (fieldType [] label target) ↔
      ∀ depth rank env obs,
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy (depth + 1) target)
          (.field label obs) →
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy (depth + 1) source)
          (.field label obs) := by
  rw [profileLe_exact]
  apply forall_congr'
  intro depth
  apply forall_congr'
  intro rank
  apply forall_congr'
  intro env
  apply forall_congr'
  intro obs
  exact imp_congr
    (by simpa only [CommonFinite.maskedProbeAt_nil] using
      (field_type_exact [] label target depth rank env obs).symm)
    (by simpa only [CommonFinite.maskedProbeAt_nil] using
      (field_type_exact [] label source depth rank env obs).symm)

theorem optionalComparison_exact (label : Nat) (source target : Common.Ty) :
    ProfileLe (optionalType [] label source) (optionalType [] label target) ↔
      ∀ depth rank env obs,
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy (depth + 1) target)
          (.optional label obs) →
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy (depth + 1) source)
          (.optional label obs) := by
  rw [profileLe_exact]
  apply forall_congr'
  intro depth
  apply forall_congr'
  intro rank
  apply forall_congr'
  intro env
  apply forall_congr'
  intro obs
  exact imp_congr
    (by simpa only [CommonFinite.maskedProbeAt_nil] using
      (optional_type_exact [] label target depth rank env obs).symm)
    (by simpa only [CommonFinite.maskedProbeAt_nil] using
      (optional_type_exact [] label source depth rank env obs).symm)

/-- Only source optional information, source presence and the proper fallback
reference are used. No whole-default type is retained in this finite payload. -/
def selectedPayload (label : Nat) (source fallback : Common.Ty) :
    Profile (CommonSyntax.State Common.Row) :=
  Profile.both (optionalProject [] label source)
    (if CommonDefaultRequired.present label source then some .bottom
      else some (.ref (.node fallback)))

def selectedField (label : Nat) (source fallback : Common.Ty) : Option Common.Ty :=
  (selectedPayload label source fallback).map Payload.common

def selectedOptional (label : Nat) (source fallback : Common.Ty) : Option Common.Ty :=
  (Profile.withTrivial (selectedPayload label source fallback)).map Payload.common

@[simp] theorem selectedField_exact (label : Nat) (source fallback : Common.Ty) :
    fieldType [] label (Common.recordDefault label source fallback) = selectedField label source fallback := by
  simp [fieldType, fieldProject, Common.recordDefault, selectedField, selectedPayload,
    CommonDefaultRequired.present]
  rfl

@[simp] theorem selectedOptional_exact (label : Nat) (source fallback : Common.Ty) :
    optionalType [] label (Common.recordDefault label source fallback) = selectedOptional label source fallback := by
  simp [optionalType, optionalProject, Common.recordDefault, selectedOptional, selectedPayload,
    CommonDefaultRequired.present]
  rfl

/-- All targets, including mixed heads, masks, defaults and regular graphs,
reduce to a finite head guard, two child-profile comparisons, and unchanged
source-tail tests. No shape or presence hypothesis is imposed on the source. -/
theorem default_target_split (label : Nat) (source fallback target : Common.Ty) :
    Common.Subtype (Common.recordDefault label source fallback) target ↔
      CommonRecordEnvelope.outsideRecords target = false ∧
        ProfileLe (selectedField label source fallback) (fieldType [] label target) ∧
        ProfileLe (selectedOptional label source fallback) (optionalType [] label target) ∧
        Common.RecordTailLe [label] source target := by
  rw [← selectedField_exact, ← selectedOptional_exact,
    fieldComparison_exact, optionalComparison_exact]
  constructor
  · intro below
    refine ⟨CommonRecordEnvelope.default_target_compatible label source fallback target below,
      ?_, ?_, ?_⟩
    · intro depth rank env obs accepted
      exact (CommonFinite.producerLe_iff_probe _ _).mp (below (depth + 1)) rank env _ accepted
    · intro depth rank env obs accepted
      exact (CommonFinite.producerLe_iff_probe _ _).mp (below (depth + 1)) rank env _ accepted
    · intro depth
      constructor
      · intro rank env current visible obs accepted
        have different : current ≠ label := by simpa using visible
        have output := (CommonFinite.producerLe_iff_probe _ _).mp (below depth) rank env _ accepted
        cases depth with
        | zero =>
            have tail := (CommonFinite.probeAt_record_field rank env label current .bottom
              (Common.observeTy 0 source) obs).mp output
            simpa only [different, ↓reduceIte] using tail
        | succ depth =>
            change CommonFinite.ProbeAt Common.rowLe rank env
              (.recordDefault label (Common.observeTy (depth + 1) source) (Common.observeTy depth fallback))
              (.field current obs) at output
            simpa only [CommonFinite.probeAt_default_field, different, ↓reduceIte] using output
      · intro rank env current visible obs nontrivial accepted
        have different : current ≠ label := by simpa using visible
        have output := (CommonFinite.producerLe_iff_probe _ _).mp (below depth) rank env _ accepted
        cases depth with
        | zero =>
            have tail := (CommonFinite.probeAt_record_optional rank env label current .bottom
              (Common.observeTy 0 source) obs).mp output
            simpa only [different, ↓reduceIte, nontrivial, or_false] using tail
        | succ depth =>
            change CommonFinite.ProbeAt Common.rowLe rank env
              (.recordDefault label (Common.observeTy (depth + 1) source) (Common.observeTy depth fallback))
              (.optional current obs) at output
            simpa only [CommonFinite.probeAt_default_optional, different, ↓reduceIte,
              nontrivial, or_false] using output
  · rintro ⟨compatible, selectedFields, selectedOptional, remaining⟩ depth
    have envelopeBelow := (CommonRecordEnvelope.envelope_below_iff target).mpr compatible depth
    rw [CommonRecordEnvelope.envelope_observe] at envelopeBelow
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have recordObs := (CommonRecordEnvelope.finiteEnvelope_probe Common.rowLe rank env obs).mp
      ((CommonFinite.producerLe_iff_probe _ _).mp envelopeBelow rank env obs accepted)
    cases obs with
    | field current inner =>
        by_cases same : current = label
        · subst current
          cases depth with
          | zero =>
              change CommonFinite.ProbeAt Common.rowLe rank env
                (.record label .bottom (Common.observeTy 0 source)) (.field label inner)
              rw [CommonFinite.probeAt_record_field]
              simp only [↓reduceIte]
              exact CommonFinite.probeAt_bottom rank inner
          | succ depth => exact selectedFields depth rank env inner accepted
        · have output := (remaining depth).1 rank env current (by simpa using same) inner accepted
          cases depth with
          | zero =>
              change CommonFinite.ProbeAt Common.rowLe rank env
                (.record label .bottom (Common.observeTy 0 source)) (.field current inner)
              simpa only [CommonFinite.probeAt_record_field, same, ↓reduceIte] using output
          | succ depth =>
              change CommonFinite.ProbeAt Common.rowLe rank env
                (.recordDefault label (Common.observeTy (depth + 1) source) (Common.observeTy depth fallback))
                (.field current inner)
              simpa only [CommonFinite.probeAt_default_field, same, ↓reduceIte] using output
    | optional current inner =>
        by_cases same : current = label
        · subst current
          cases depth with
          | zero =>
              change CommonFinite.ProbeAt Common.rowLe rank env
                (.record label .bottom (Common.observeTy 0 source)) (.optional label inner)
              rw [CommonFinite.probeAt_record_optional]
              simp only [↓reduceIte]
              exact CommonFinite.probeAt_bottom rank inner
          | succ depth => exact selectedOptional depth rank env inner accepted
        · have output : CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source)
                (.optional current inner) ∨ inner = .trivial := by
            by_cases trivial : inner = .trivial
            · exact Or.inr trivial
            · exact Or.inl ((remaining depth).2 rank env current (by simpa using same)
                inner trivial accepted)
          cases depth with
          | zero =>
              change CommonFinite.ProbeAt Common.rowLe rank env
                (.record label .bottom (Common.observeTy 0 source)) (.optional current inner)
              simpa only [CommonFinite.probeAt_record_optional, same, ↓reduceIte] using output
          | succ depth =>
              change CommonFinite.ProbeAt Common.rowLe rank env
                (.recordDefault label (Common.observeTy (depth + 1) source) (Common.observeTy depth fallback))
                (.optional current inner)
              simpa only [CommonFinite.probeAt_default_optional, same, ↓reduceIte] using output
    | trivial => exact CommonFinite.probeAt_trivial rank _
    | records => cases depth <;> cases rank <;> trivial
    | role name => cases depth <;> cases rank <;> exact recordObs
    | _ => exact False.elim recordObs

end Yulang.CommonDefaultTargetSplit
