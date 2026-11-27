import Yulang.GeneralDeclarativeI65I74LiteralSuppliedProjection464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open PreparedDeclarations463
open GeneralDeclarativeK2Graph321.AddAtOneSource

structure LiteralFieldWire (p : SnapshotPair) where
  projected : List LiteralProjectionWire
  field : HeadFieldWire p.after.old

/-- A support reader over two *supplied* snapshots. Its structural visits
are exactly the existing HeadField reader; a literal proposal does not
authorize any constructor opening or create its raw row or native issuer. -/
def readLiteralProjectionField (p : SnapshotPair) (tab : CheckedTable p.before.state.base.core.current)
    (w : LiteralFieldWire p) : Option HeadFieldReceipt := do
  if !checkLiteralSuppliedPhase p.pre p.post w.projected then none else
    let receipt ← readHeadField (p := p.after.old) (p.afterTable tab) w.field
    if receipt.rows.any (fun i => decide (p.pre.equations.length ≤ i)) then some receipt else none

def ExactLiteralProjectedField (p : SnapshotPair) (tab : CheckedTable p.before.state.base.core.current)
    (plans : List SourceRowSelection) (r : HeadFieldReceipt) : Prop :=
  OrderedSafeAppends p.pre (suppliedRows p.pre p.post) p.post ∧
    OriginalLiteralPlans p.pre plans (suppliedRows p.pre p.post) ∧
    ExactHeadField (p := p.after.old) (p.afterTable tab) r ∧
    ∃ i ∈ r.rows, p.pre.equations.length ≤ i

theorem exact_literal_and_structural_receipt_has_finite_wire
    (p : SnapshotPair) (tab : CheckedTable p.before.state.base.core.current)
    (plans : List SourceRowSelection) (r : HeadFieldReceipt) :
    ExactLiteralProjectedField p tab plans r ↔
    ∃ w, w.projected.map LiteralProjectionWire.source = plans ∧
      readLiteralProjectionField p tab w = some r := by
  constructor
  · rintro ⟨safe,source,field,used⟩
    obtain ⟨wire,sourceData,checked⟩ :=
      (exact_original_row_plans_have_finite_supplied_phase_certificate ..).mpr ⟨safe,source⟩
    obtain ⟨f,lookup⟩ := (prechecked_head_field_iff_finite_exact_wire ..).mp field
    exact ⟨⟨wire,f⟩,sourceData,by simp [readLiteralProjectionField,checked,lookup,used,Option.bind]⟩
  · rintro ⟨w,rfl,pass⟩
    by_cases phase : checkLiteralSuppliedPhase p.pre p.post w.projected = true
    · cases out : readHeadField (p := p.after.old) (p.afterTable tab) w.field with
      | none => simp [readLiteralProjectionField,phase,out,Option.bind] at pass
      | some read =>
        by_cases used : ∃ i ∈ read.rows, p.pre.equations.length ≤ i
        · have same : read = r := by
            simpa [readLiteralProjectionField,phase,out,used,Option.bind] using pass
          cases same
          have exactPhase := accepted_literal_phase_has_exact_ordinary_batch_and_original_plans phase
          exact ⟨exactPhase.1.1,exactPhase.2,(prechecked_head_field_iff_finite_exact_wire ..).mpr
            ⟨_,out⟩,used⟩
        · simp [readLiteralProjectionField,phase,out,used,Option.bind] at pass
    · simp [readLiteralProjectionField,phase] at pass

theorem literal_field_success_uses_exact_existing_structural_reader_and_supported_ordinary_batch
    {p : SnapshotPair} {tab : CheckedTable p.before.state.base.core.current}
    {w : LiteralFieldWire p} {r : HeadFieldReceipt} (h : readLiteralProjectionField p tab w = some r) :
    readHeadField (p := p.after.old) (p.afterTable tab) w.field = some r ∧
    ExactProjectionBatchField p tab r := by
  by_cases phase : checkLiteralSuppliedPhase p.pre p.post w.projected = true
  · cases out : readHeadField (p := p.after.old) (p.afterTable tab) w.field with
    | none => simp [readLiteralProjectionField,phase,out,Option.bind] at h
    | some read =>
      by_cases used : ∃ i ∈ read.rows, p.pre.equations.length ≤ i
      · have same : read = r := by
          simpa [readLiteralProjectionField,phase,out,used,Option.bind] using h
        cases same
        exact ⟨rfl,(accepted_literal_phase_has_exact_ordinary_batch_and_original_plans phase).1,
          (prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨w.field,out⟩,used⟩
      · simp [readLiteralProjectionField,phase,out,used,Option.bind] at h
  · simp [readLiteralProjectionField,phase] at h

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
