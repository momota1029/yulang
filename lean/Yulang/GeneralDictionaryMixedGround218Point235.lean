import Yulang.GeneralDictionaryMixedGround218Reobserve235
import Yulang.GeneralDictionaryMixedGround218Rejection235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGround218Point235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryMixedGround218Leaf235 (ctx oldChild)
open GeneralDictionaryMixedGround218Install234 (installed)
open GeneralDictionaryMixedGround218Reobserve235
noncomputable abbrev allocated := ctx.state.allocated
noncomputable abbrev reserved := ctx.state.reserved
noncomputable abbrev ordinary := ctx.state.ordinary

theorem context_same : installed.core.erased.current.context.state =
    GeneralDictionaryGroundCopy218Reobserve.looseExtended allocated reserved ordinary := rfl
noncomputable abbrev point := result allocated reserved ordinary context_same

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root installed point :=
  GeneralDictionaryMixedGround218Reobserve235.step rfl allocated reserved ordinary context_same registry root

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root point := by
  obtain ⟨start,initial,path⟩ := GeneralDictionaryMixedGround218Install234.reachable
  exact ⟨start,initial,.tail path step⟩

theorem models_iff (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalVersionedJournal232.Models point model ↔ GeneralNominalVersionedJournal232.Models installed model :=
  GeneralDictionaryMixedGround218Reobserve235.models_iff rfl allocated reserved ordinary context_same model

theorem point_model : GeneralNominalVersionedJournal232.Models point GeneralDictionaryGroundCopy218Install.model :=
  (models_iff _).mpr GeneralDictionaryMixedGround218Install234.installed_model

theorem point_snapshot : point.core.erased.current.context.state =
    GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved ordinary :=
  current_snapshot allocated reserved ordinary context_same

theorem no_reobserve (revision : GeneralNominalReobservationSteps.Revision point.core.erased.current) :
    ¬ GeneralNominalReobservationSteps.Improves revision := by
  apply GeneralNominalReobservationSteps.pointClosed_no_revision
  rw [point_snapshot]
  exact GeneralDictionaryGroundCopy218Reobserve.point_closed allocated reserved ordinary

theorem installed_not_stable : ¬ GeneralNominalVersionedMixedKernel234.Stable registry installed root := by
  intro stable
  obtain ⟨focus,generated,action⟩ := step
  exact stable focus generated point action
end Yulang.GeneralDictionaryMixedGround218Point235
