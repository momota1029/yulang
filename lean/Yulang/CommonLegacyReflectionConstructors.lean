import Yulang.CommonLegacyReflection

/-!
# Constructor boundary interpolation with mixed variance

The common children below remain arbitrary. Comparison to a fixed old pair,
tag or arrow can be reflected after the finite upper tests of its positive
children have been included. In the opposite direction the arrow's negative
child needs an upper test instead. All old lower comparisons are preserved
without a test-membership condition, and all four arrow rows are unchanged.

These lemmas identify the tests required at one constructor boundary. They
do not claim that applying a finite envelope independently to every node
preserves the shared constructor equations of a generated graph.
-/

namespace Yulang.CommonLegacyReflection

open Common (Subtype embedOld)

def oldPair (first last : OldTy) : OldTy := .pair (.node first) (.node last)
def oldVariant (label : Nat) (payload : OldTy) : OldTy := .variant label (.node payload)
def oldArrow (input : OldTy) (incoming : Common.Row) (output : OldTy)
    (outgoing : Common.Row) : OldTy := .arrow (.node input) incoming (.node output) outgoing

/-- Both fixed positive component tests suffice; no restriction is placed
on either common child. -/
theorem pair_upper_reflected (tests : List OldTy) (first last : Common.Ty)
    (firstBound lastBound : OldTy) (firstTest : firstBound ∈ tests) (lastTest : lastBound ∈ tests)
    (below : Subtype (Common.pair first last)
      (Common.pair (embedOld firstBound) (embedOld lastBound))) :
    OldLe (oldPair (envelope tests first) (envelope tests last)) (oldPair firstBound lastBound) := by
  obtain ⟨before, after⟩ := (Common.common_pair_iff _ _ _ _).mp below
  exact (ProducerContextualRegular.producerLe_pair_iff _ _ _ _).mpr
    ⟨(envelope_upper_exact tests first firstBound firstTest).mpr before,
      (envelope_upper_exact tests last lastBound lastTest).mpr after⟩

theorem pair_lower_reflected (tests : List OldTy) (first last : Common.Ty)
    (firstBound lastBound : OldTy)
    (below : Subtype (Common.pair (embedOld firstBound) (embedOld lastBound))
      (Common.pair first last)) :
    OldLe (oldPair firstBound lastBound) (oldPair (envelope tests first) (envelope tests last)) := by
  obtain ⟨before, after⟩ := (Common.common_pair_iff _ _ _ _).mp below
  exact (ProducerContextualRegular.producerLe_pair_iff _ _ _ _).mpr
    ⟨envelope_preserves_lower tests first firstBound before,
      envelope_preserves_lower tests last lastBound after⟩

theorem variant_upper_reflected (tests : List OldTy) (label : Nat) (payload : Common.Ty)
    (bound : OldTy) (available : bound ∈ tests)
    (below : Subtype (Common.variant label payload) (Common.variant label (embedOld bound))) :
    OldLe (oldVariant label (envelope tests payload)) (oldVariant label bound) :=
  (ProducerContextualRegular.producerLe_variant_iff label _ _).mpr
    ((envelope_upper_exact tests payload bound available).mpr
      ((Common.common_variant_iff label _ _).mp below))

theorem variant_lower_reflected (tests : List OldTy) (label : Nat) (payload : Common.Ty)
    (bound : OldTy)
    (below : Subtype (Common.variant label (embedOld bound)) (Common.variant label payload)) :
    OldLe (oldVariant label bound) (oldVariant label (envelope tests payload)) :=
  (ProducerContextualRegular.producerLe_variant_iff label _ _).mpr
    (envelope_preserves_lower tests payload bound
      ((Common.common_variant_iff label _ _).mp below))

/-- The input obligation is a lower bound on the unknown, so only the old
output is required in the upper-test family. Rows remain independent. -/
theorem arrow_upper_reflected (tests : List OldTy) (input output : Common.Ty)
    (inputBound outputBound : OldTy) (incoming outgoing incomingBound outgoingBound : Common.Row)
    (outputTest : outputBound ∈ tests)
    (below : Subtype (Common.arrow input incoming output outgoing)
      (Common.arrow (embedOld inputBound) incomingBound (embedOld outputBound) outgoingBound)) :
    OldLe (oldArrow (envelope tests input) incoming (envelope tests output) outgoing)
      (oldArrow inputBound incomingBound outputBound outgoingBound) := by
  obtain ⟨argument, inputRow, result, outputRow⟩ :=
    (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp below
  exact (ProducerContextualRegular.producerLe_arrow_iff Common.rowLe_refl Common.rowLe_trans
    _ _ _ _ _ _ _ _).mpr
    ⟨envelope_preserves_lower tests input inputBound argument, inputRow,
      (envelope_upper_exact tests output outputBound outputTest).mpr result, outputRow⟩

/-- With the old constructor on the left, the negative input becomes the
upper test. The output lower bound needs no membership assumption. -/
theorem arrow_lower_reflected (tests : List OldTy) (input output : Common.Ty)
    (inputBound outputBound : OldTy) (incoming outgoing incomingBound outgoingBound : Common.Row)
    (inputTest : inputBound ∈ tests)
    (below : Subtype
      (Common.arrow (embedOld inputBound) incomingBound (embedOld outputBound) outgoingBound)
      (Common.arrow input incoming output outgoing)) :
    OldLe (oldArrow inputBound incomingBound outputBound outgoingBound)
      (oldArrow (envelope tests input) incoming (envelope tests output) outgoing) := by
  obtain ⟨argument, inputRow, result, outputRow⟩ :=
    (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp below
  exact (ProducerContextualRegular.producerLe_arrow_iff Common.rowLe_refl Common.rowLe_trans
    _ _ _ _ _ _ _ _).mpr
    ⟨(envelope_upper_exact tests input inputBound inputTest).mpr argument, inputRow,
      envelope_preserves_lower tests output outputBound result, outputRow⟩

theorem envelope_top_test (source : Common.Ty) :
    envelope [.top] source = .inter .top .top := by
  classical
  have accepted : Subtype source (embedOld .top) := CommonBoundCoalescing.le_top source
  simp [envelope, accepted, meet]

/-- Even the complete component list of the old target `top` does not make
independent node interpolation preserve a pair equation. This refutes that
proof shortcut, not the supported-source reflection contract. -/
theorem envelope_does_not_preserve_pair_equation (first last : Common.Ty) :
    ¬ OldLe (envelope [.top] (Common.pair first last))
      (oldPair (envelope [.top] first) (envelope [.top] last)) := by
  rw [envelope_top_test, envelope_top_test, envelope_top_test]
  intro below
  have atZero := (ProducerContextual.producerLe_iff_probe _ _).mp (below 0)
    0 ⟨fun _ => .bottom, fun _ => []⟩ (.pairFirst .trivial) (by
      simp [oldPair, RegularValueTypes.Layer.eval, RegularValueTypes.observe,
        ProducerContextual.ProbeAt, ProducerContextual.ProbeStep])
  simp [RegularValueTypes.Layer.eval, ProducerContextual.ProbeAt,
    ProducerContextual.ProbeStep] at atZero

end Yulang.CommonLegacyReflection
