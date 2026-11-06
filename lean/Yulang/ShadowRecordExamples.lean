import Yulang.ShadowRecordQuotientInference
import Yulang.RigidRecordSourceBoundary

/-!
# Previously separated source instances become equal under decision 40

The source expression and the historical negative theorems are unchanged.
Both old instances are preserved, but their result types now represent the
same element of the semantic quotient, for any row join algebra.
-/

namespace Yulang.ShadowRecordExamples

open Inference
open StructuralBase (Ty)
open ShadowSemanticRecords (Subtype Equivalent)
open RigidRecordSourceBoundary (expression nested flat)

universe u

variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  ShadowRecordQuotientInference.model algebra

theorem boundary_equivalent (leRow : Row → Row → Prop) :
    Equivalent leRow (nested : Ty Row) flat :=
  ShadowSemanticRecords.shadow_equivalent 0 (.base .int) (.base .str) _

theorem boundary_quotient_equal (leRow : Row → Row → Prop) :
    ShadowRecordQuotient.mk (leRow := leRow) (nested : Ty Row) =
      ShadowRecordQuotient.mk flat :=
  Quotient.sound (boundary_equivalent leRow)

theorem source_has_equal_instances (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] expression (ShadowRecordQuotient.mk nested, algebra.empty) ∧
      Typing (model algebra) [] expression (ShadowRecordQuotient.mk flat, algebra.empty) ∧
      ShadowRecordQuotient.mk (leRow := algebra.le) (nested : Ty Row) =
        ShadowRecordQuotient.mk flat := by
  have first := ShadowRecordInference.rigid_closed_typing_preserved
    algebra.empty algebra.join algebra.le expression (nested, algebra.empty)
    (RigidRecordSourceBoundary.typed_nested algebra)
  have last := ShadowRecordInference.rigid_closed_typing_preserved
    algebra.empty algebra.join algebra.le expression (flat, algebra.empty)
    (RigidRecordSourceBoundary.typed_flat algebra)
  exact ⟨(ShadowRecordQuotientInference.closed_typing_exact
      algebra.empty algebra.join algebra.le algebra.refl expression _).mpr first,
    (ShadowRecordQuotientInference.closed_typing_exact
      algebra.empty algebra.join algebra.le algebra.refl expression _).mpr last,
    boundary_quotient_equal algebra.le⟩

/-- The actual all-core graph compiler retains the identified source instance. -/
theorem compiled_boundary_instance (algebra : RowFlowSchemes.Algebra Row) :
    OpenRecordConstraintGraph.SourceInstance (model algebra)
      (OpenRecordConstraintGraph.compileSource expression)
      (ShadowRecordQuotient.mk flat, algebra.empty) :=
  (ShadowRecordQuotientInference.compiled_typing_exact algebra expression _).mpr
    (source_has_equal_instances algebra).2.1

/-- Lattice syntax in the tail does not block hidden-field equality. -/
theorem shadow_under_union_bottom (leRow : Row → Row → Prop)
    (label : Nat) (visible hidden rest : Ty Row) :
    Equivalent leRow
      (.record label visible (.union (.record label hidden rest) .bottom))
      (.record label visible rest) :=
  (ShadowSemanticRecords.record_tail_union_bottom label visible
      (.record label hidden rest)).trans
    (ShadowSemanticRecords.shadow_equivalent label visible hidden rest)

theorem visible_payload_stays_distinct (leRow : Row → Row → Prop) :
    ShadowRecordQuotient.mk (leRow := leRow) (.base .int) ≠
      ShadowRecordQuotient.mk (.base .str) :=
  ShadowRecordQuotient.int_ne_str

end Yulang.ShadowRecordExamples
