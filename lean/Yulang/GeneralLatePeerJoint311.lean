import Yulang.GeneralLatePeerRecursive311
import Yulang.GeneralVersionedCheckedResidual310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralLatePeerJoint311
open GeneralLatePeerSource311 (compiled checked registry)
open GeneralLatePeerRoot311 (z)
open GeneralLatePeerRoutePlan311 (child)
open GeneralLatePeerMerge311 (final reached inherited)
open GeneralLatePeerFinalPeerPlan311 (plan)
open GeneralLatePeerCurrent311 (frame known picked classes inhabited)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)

abbrev effect := GeneralLatePeerGuard311.effect (p := plan) reached frame known

theorem not_locally_represented :
    ¬ GeneralVersionedCheckedResidual310.Represented final child.occurrence := by
  intro full
  obtain ⟨localReq,localMember,_⟩ := full ⟨1,z⟩ inherited
  cases localMember

theorem jointly (m : Assignment) (valid : Models final m) :
    GeneralNominalVersionedInstall232.InstallationModels final effect m := by
  apply (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ reached rfl rfl).mpr
  exact ⟨valid,GeneralLatePeerFinalPeerPlan311.holds m valid,classes m valid⟩

/-- The choice proof here is the actual distinct historical transfer; the
    joint witness is the same live model, not the aggregate patch of choice. -/
theorem enabled : GeneralNominalVersionedMixedKernel234.Installable compiled final effect := by
  apply (GeneralNominalVersionedMixedSelectedEffect235.source_installable_iff reached picked rfl rfl).mpr
  exact ⟨GeneralLatePeerTransfer311.compatible,_,jointly _ inhabited⟩
end Yulang.GeneralLatePeerJoint311
