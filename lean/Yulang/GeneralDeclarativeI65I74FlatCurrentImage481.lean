import Yulang.GeneralDeclarativeI65I74FlatRoundtrip481

namespace Yulang.GeneralDeclarativeI65.I72.Flat481
open RetainedFull445 (FullProblem)
open HomogeneousClosedEntry459 (Report Witness)

def InCurrentReportImage : FlatReport → Prop
  | .legacy scope _ => scope = .guardedWhere
  | _ => True

/-- Early legacy envelopes retain their earlier classification domain; only
its guarded-where grade belongs to the last historical report image. -/
theorem current_report_right_inverse481 (r : FlatReport) (range : InCurrentReportImage r) :
    (unflattenFieldHomogeneousReport r).map flattenFieldHomogeneousReport = some r := by
  cases r <;> try rfl
  case legacy scope r =>
    change scope = .guardedWhere at range
    subst scope
    rfl

theorem current_wire_right_inverse481 (w : FlatWitness) :
    (unflattenFieldHomogeneousWire w).map flattenFieldHomogeneousWire = some w := by
  cases w <;> try rfl
  case legacy w => cases w <;> rfl

/-- Reification is exact on the last historical report envelope, including failures. -/
theorem flat_data_and_current_entry_are_exactly_equivalent481 (p : FullProblem)
    (r : FlatReport) (w : FlatWitness) (range : InCurrentReportImage r) :
    ∃ rOld : Report, ∃ wOld : Witness,
      unflattenFieldHomogeneousReport r = some rOld ∧
      unflattenFieldHomogeneousWire w = some wOld ∧
      flattenFieldHomogeneousReport rOld = r ∧
      flattenFieldHomogeneousWire wOld = w ∧
      check_full_flat p r w = HomogeneousClosedEntry459.check_full_homogeneous459 p rOld wOld := by
  have backR := current_report_right_inverse481 r range
  have backW := current_wire_right_inverse481 w
  cases gotR : unflattenFieldHomogeneousReport r with
  | none => simp [gotR] at backR
  | some rr =>
    cases gotW : unflattenFieldHomogeneousWire w with
    | none => simp [gotW] at backW
    | some ww =>
      simp only [gotR, Option.map_some, Option.some.injEq] at backR
      simp only [gotW, Option.map_some, Option.some.injEq] at backW
      exact ⟨rr,ww,rfl,rfl,backR,backW,
        backR ▸ backW ▸ fieldHomogeneous_same_Bool481 p rr ww⟩

theorem current_report_image_is_exact481 (r : FlatReport) :
    InCurrentReportImage r ↔ (unflattenFieldHomogeneousReport r).isSome = true := by
  cases r <;> simp [InCurrentReportImage, unflattenGroupedReport, unflattenRawGroupedReport, unflattenFieldRecordReport, unflattenFieldMixedReport, unflattenFieldNominalReport, unflattenFieldReadyRecordReport, unflattenFieldReadyMixedReport, unflattenFieldVariantReport, unflattenFieldStructuralReport, unflattenFieldProjectedReport, unflattenFieldHomogeneousReport, unflattenLegacyReport, FlatReport.tier]

theorem flat_current_report_codec_injective481 :
    Function.Injective flattenFieldHomogeneousReport := by
  intro a b same
  have eq := congrArg unflattenFieldHomogeneousReport same
  rw [fieldHomogeneous_report_roundtrip481,fieldHomogeneous_report_roundtrip481] at eq
  exact Option.some.inj eq

theorem flat_current_wire_codec_injective481 :
    Function.Injective flattenFieldHomogeneousWire := by
  intro a b same
  have eq := congrArg unflattenFieldHomogeneousWire same
  rw [fieldHomogeneous_wire_roundtrip481,fieldHomogeneous_wire_roundtrip481] at eq
  exact Option.some.inj eq
end Yulang.GeneralDeclarativeI65.I72.Flat481
