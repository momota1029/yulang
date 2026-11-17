import Yulang.GeneralNominalVersionedMixedKernel234
/-! I45: an observation revision may refine nonpoint nominal descriptors,
but may not retarget a descriptor already determined at a point. Literal
source descriptors are preserved, not merely equivalent semantic values. -/
namespace Yulang.GeneralNominalPointRevision240
open GeneralNominalReobservationSteps
variable {roles : Roles.RoleDecls}

def Preserves (revision : Revision (state : GeneralNominalSaturationState.State roles)) : Prop :=
 ∀ slot descriptor, state.context.state.nominals slot = some descriptor →
   PointDescriptor descriptor → revision.entries slot = some descriptor

variable {state : GeneralNominalSaturationState.State roles} {revision : Revision state}

theorem point_unchanged (preserved : Preserves revision)
 (point : PointAt state.context.state slot) :
 revision.entries slot = state.context.state.nominals slot := by
 obtain ⟨descriptor,found,determined⟩ := point
 rw [found]
 exact preserved slot descriptor found determined

theorem point_retained (preserved : Preserves revision) (point : PointAt state.context.state slot) :
 PointAt revision.snapshot slot := by
 obtain ⟨descriptor,found,determined⟩ := point
 exact ⟨descriptor,preserved slot descriptor found determined,determined⟩
end Yulang.GeneralNominalPointRevision240
