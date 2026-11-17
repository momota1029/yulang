import Yulang.GeneralDictionaryVersionedInitialFrame233
import Yulang.GeneralDictionaryVersionedReobserve233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedPointStage233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInitialFrame233
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralNominalVersionedJournal232

noncomputable abbrev allocated := installed.core.erased.current.context.state.allocated
noncomputable abbrev reserved := installed.core.erased.current.context.state.reserved
noncomputable abbrev ordinary := installed.core.erased.current.context.state.ordinary

theorem current_loose : installed.core.erased.current.context.state = looseExtended allocated reserved ordinary := rfl

noncomputable def revision := GeneralDictionaryVersionedReobserve233.revision allocated reserved ordinary current_loose
noncomputable def point := GeneralDictionaryVersionedReobserve233.result allocated reserved ordinary current_loose

theorem step : GeneralNominalVersionedKernel232.Step registry root installed point :=
  GeneralDictionaryVersionedReobserve233.step rfl allocated reserved ordinary current_loose registry root

theorem models_iff (model : GeneralNominalCommonBridge.Assignment) : Models point model ↔ Models installed model :=
  GeneralDictionaryVersionedReobserve233.models_iff rfl allocated reserved ordinary current_loose model

theorem inhabited : Models point GeneralDictionaryVersionedInitialModel233.extended :=
  (models_iff _).mpr installed_model

theorem context_exact : point.core.erased.current.context =
    GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary := rfl

theorem raw_sites : point.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := by
  change (GeneralNominalVersionedInstall232.installCore before.core effect.plan).erased.current.sites = _
  rw [GeneralNominalVersionedTerminal232.raw_eq children_empty]
  rfl

theorem centered_sites : point.core.sites = [GeneralNominalCenters.rootSite snapshot.seed root] := by
  change (GeneralNominalVersionedInstall232.installCore before.core effect.plan).sites = _
  rw [GeneralNominalVersionedTerminal232.sites_eq children_empty]
  rfl

theorem point_closed : GeneralNominalReobservationSteps.PointClosed point.core.erased.current.context.state :=
  GeneralDictionaryJournalRefinement228Reobserve.point_closed allocated reserved ordinary

theorem no_second_reobserve (next : GeneralNominalReobservationSteps.Revision point.core.erased.current) :
    ¬ GeneralNominalReobservationSteps.Improves next :=
  GeneralNominalReobservationSteps.pointClosed_no_revision point_closed next

theorem original_plan_retained : GeneralDictionaryOptionalInstall229.plan ∈ point.plans := List.mem_cons_self ..
theorem original_effect_retained : effect ∈ point.effects := List.mem_cons_self ..

end Yulang.GeneralDictionaryVersionedPointStage233
