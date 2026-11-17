import Yulang.GeneralNominalVersionedEvidence231
set_option backward.isDefEq.respectTransparency false

/-! Structural frame transport and exact request-class transport. No new
model, packet satisfaction, operational step, or global soundness is inferred
from context equality alone. -/
namespace Yulang.GeneralNominalVersionedFrameTransport232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedEvidence231
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadOutputs (requests)
variable {roles : Roles.RoleDecls}

theorem frame_forward {before after : GeneralNominalCenteredSteps.State roles}
    (context : before.erased.current.context = after.erased.current.context)
    (raw : before.erased.current.sites ⊆ after.erased.current.sites)
    (centers : before.sites ⊆ after.sites)
    (frame : Frame registry before root key plan) : Frame registry after root key plan where
  registry_eq := frame.registry_eq
  context_eq := frame.context_eq.trans context
  occurrence_eq := frame.occurrence_eq
  key_eq := frame.key_eq
  raw_recorded := raw frame.raw_recorded
  center_recorded := centers frame.center_recorded
  visible := frame.visible
  role_eq := frame.role_eq
  located := frame.located
  prepared := context ▸ frame.prepared

/-- Membership equality suffices; ordering and duplicate requests are irrelevant. -/
theorem ready_iff {before after : GeneralNominalCenteredSteps.State roles}
    (same : ∀ output, output ∈ requests before root ↔ output ∈ requests after root) :
    GeneralNominalCenteredHeadMatEffects.Ready before root plan ↔
      GeneralNominalCenteredHeadMatEffects.Ready after root plan := by
  unfold GeneralNominalCenteredHeadMatEffects.Ready
  simp only [same]

theorem class_effects_iff {before after : GeneralNominalCenteredSteps.State roles}
    (same : ∀ output, output ∈ requests before root ↔ output ∈ requests after root) :
    GeneralNominalVersionedEffects231.ClassEffects before root plan model ↔
      GeneralNominalVersionedEffects231.ClassEffects after root plan model := by
  unfold GeneralNominalVersionedEffects231.ClassEffects GeneralNominalCenteredHeadOutputs.EqualOutputs
  simp only [same]

theorem schema_holds_iff {before after : GeneralNominalCenteredSteps.State roles}
    (same : ∀ output, output ∈ requests before root ↔ output ∈ requests after root) :
    GeneralNominalVersionedEffects231.SchemaHolds before root plan model ↔
      GeneralNominalVersionedEffects231.SchemaHolds after root plan model := by
  unfold GeneralNominalVersionedEffects231.SchemaHolds
  rw [class_effects_iff same]

theorem ready_of_requests_eq {before after : GeneralNominalCenteredSteps.State roles}
    (same : requests before root = requests after root) :
    GeneralNominalCenteredHeadMatEffects.Ready before root plan ↔
      GeneralNominalCenteredHeadMatEffects.Ready after root plan :=
  ready_iff (fun _ => same ▸ Iff.rfl)

theorem class_effects_of_requests_eq {before after : GeneralNominalCenteredSteps.State roles}
    (same : requests before root = requests after root) :
    GeneralNominalVersionedEffects231.ClassEffects before root plan model ↔
      GeneralNominalVersionedEffects231.ClassEffects after root plan model :=
  class_effects_iff (fun _ => same ▸ Iff.rfl)

/-- Local certificate transport only: the old certificate is an explicit
premise, and no new child evidence or applicability is fabricated. -/
theorem certificate_forward {before after : GeneralNominalCenteredSteps.State roles}
    (context : before.erased.current.context = after.erased.current.context)
    (raw : before.erased.current.sites ⊆ after.erased.current.sites)
    (centers : before.sites ⊆ after.sites)
    (source : Certificate registry before model root key children plan) :
    Certificate registry after model root key children plan :=
  ⟨frame_forward context raw centers source.frame,source.children_eq,source.packet,source.outputs⟩

theorem instance_forward {before after : GeneralNominalCenteredSteps.State roles}
    (context : before.erased.current.context = after.erased.current.context)
    (raw : before.erased.current.sites ⊆ after.erased.current.sites)
    (centers : before.sites ⊆ after.sites)
    (source : Instance registry before model root key children) :
    Instance registry after model root key children := by
  obtain ⟨plan,source⟩ := source
  exact ⟨plan,certificate_forward context raw centers source⟩

end Yulang.GeneralNominalVersionedFrameTransport232
