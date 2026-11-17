import Yulang.GeneralDictionaryCompoundStep238
import Yulang.GeneralDictionaryCompoundCurrent238
import Yulang.GeneralNominalVersionedMixedEmbedding234
import Yulang.GeneralDictionaryVersionedReobserve233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundPoint238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundFrame238
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralNominalVersionedJournal232

noncomputable abbrev allocated := installed.core.erased.current.context.state.allocated
noncomputable abbrev reserved := installed.core.erased.current.context.state.reserved
noncomputable abbrev ordinary := installed.core.erased.current.context.state.ordinary

theorem current_loose : installed.core.erased.current.context.state = looseExtended allocated reserved ordinary := rfl

noncomputable def revision := GeneralDictionaryVersionedReobserve233.revision allocated reserved ordinary current_loose
noncomputable def point := GeneralDictionaryVersionedReobserve233.result allocated reserved ordinary current_loose

theorem legacy_step : GeneralNominalVersionedKernel232.Step registry root installed point :=
  GeneralDictionaryVersionedReobserve233.step rfl allocated reserved ordinary current_loose registry root

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root installed point :=
  GeneralNominalVersionedMixedKernel234.old_step legacy_step

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root point := by
  obtain ⟨start,initial,path⟩ := GeneralDictionaryCompoundStep238.reachable
  exact ⟨start,initial,.tail path step⟩

theorem models_iff (model : GeneralNominalCommonBridge.Assignment) : Models point model ↔ Models installed model :=
  GeneralDictionaryVersionedReobserve233.models_iff rfl allocated reserved ordinary current_loose model

theorem inhabited : Models point GeneralDictionaryCompoundVersionedModel238.extended :=
  (models_iff _).mpr GeneralDictionaryCompoundStep238.installed_model

theorem context_exact : point.core.erased.current.context =
    GeneralDictionaryCompoundCurrent238.currentContext allocated reserved ordinary := rfl

theorem point_closed : GeneralNominalReobservationSteps.PointClosed point.core.erased.current.context.state :=
  GeneralDictionaryJournalRefinement228Reobserve.point_closed allocated reserved ordinary

theorem no_second_reobserve (next : GeneralNominalReobservationSteps.Revision point.core.erased.current) :
    ¬ GeneralNominalReobservationSteps.Improves next :=
  GeneralNominalReobservationSteps.pointClosed_no_revision point_closed next

theorem original_plan_retained : GeneralDictionaryCompoundPacket238.plan ∈ point.plans := List.mem_cons_self ..
theorem original_effect_retained : effect ∈ point.effects := List.mem_cons_self ..

end Yulang.GeneralDictionaryCompoundPoint238
