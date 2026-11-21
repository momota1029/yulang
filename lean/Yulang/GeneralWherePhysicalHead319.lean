import Yulang.GeneralWherePhysicalPatch319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 27000000
namespace Yulang.GeneralWherePhysicalHead319
open GeneralWherePhysicalPatch319 (n compatible_update)
open GeneralWherePhysicalCurrentRead319 (plan packet same bindings)
open GeneralWherePhysicalPast319 (point)
open GeneralWhereOriginSingleSource318 (newPlan newer)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralNominalVersionedPlans231 (HeadModels private_models_iff)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralWherePhysicalOldValues319 (old_head)
open CommonNominalFullCarrier

theorem now_at_w : HeadModels newer w := by
  apply GeneralWhereOriginSingleHead318.new_head w
  exact ⟨(private_models_iff ..).mpr
    ⟨GeneralLiveCompoundLeafProof316.valid.1.1,GeneralLiveCompoundPostRootHead316.ordinary_pre⟩,
    GeneralLiveCompoundPostRootHead316.projection_pre⟩

theorem new_head : HeadModels newer n :=
  (GeneralWhereOriginHeadAgree318.preserve_heads w old_head now_at_w).2

theorem current_head : HeadModels packet n := by
  have old := (private_models_iff ..).mp new_head.1
  exact ⟨(private_models_iff ..).mpr ⟨compatible_update.1.1.1,
      (GeneralDeferredLadderTransport302.ordinary_iff same n).mp old.2⟩,
    (GeneralNominalCenteredHeadMatPlanData.projections same n).mp new_head.2⟩

end Yulang.GeneralWherePhysicalHead319
