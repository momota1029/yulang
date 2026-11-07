import Yulang.CommonEffectRankMonotonicity
import Yulang.CommonDefault

/-! A route obstruction, NOT a counterexample to either B3 objective.
Negative-rank compactness cannot be reused as constructor-depth compactness
on arbitrary Common types without a separate proof. The depth-zero default
approximation deliberately has a field even for a non-record base. -/
namespace Yulang.CommonEffectDepthBoundary
open Common (Ty Row)
open CommonFinite (ProducerLe ProbeAt ProbeStep MaskedProbeStep)

def badDefault : Ty := Common.recordDefault 0 (.base .int) (.base .unit)

theorem at_one : ProducerLe Common.rowLe (Common.observeTy 1 Common.emptyRecord) (Common.observeTy 1 badDefault) := by
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank environment observation accepted
  change ProbeAt Common.rowLe rank environment (.recordDefault 0 (.base .int) (.base .unit)) observation at accepted
  change ProbeAt Common.rowLe rank environment .emptyRecord observation
  cases rank <;> cases observation <;> simp_all [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals split at * <;> simp_all [MaskedProbeStep]

theorem not_at_zero : ¬ ProducerLe Common.rowLe (Common.observeTy 0 Common.emptyRecord) (Common.observeTy 0 badDefault) := by
  intro below
  let environment : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have field : ProbeAt Common.rowLe 0 environment (Common.observeTy 0 badDefault) (.field 0 .impossible) := by
    simp [Common.observeTy, badDefault, Common.recordDefault, CommonSyntax.Layer.evalAt, ProbeAt, ProbeStep, MaskedProbeStep]
  have impossible := (CommonFinite.producerLe_iff_probe _ _).mp below 0 environment (.field 0 .impossible) field
  exact impossible

theorem depth_drop_fails :
    ¬ (∀ source target : Ty, ProducerLe Common.rowLe (Common.observeTy 1 source) (Common.observeTy 1 target) →
      ProducerLe Common.rowLe (Common.observeTy 0 source) (Common.observeTy 0 target)) :=
  fun drop => not_at_zero (drop Common.emptyRecord badDefault at_one)

end Yulang.CommonEffectDepthBoundary
