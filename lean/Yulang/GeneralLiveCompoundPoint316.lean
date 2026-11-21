import Yulang.GeneralLiveCompoundInstall316

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 22000
namespace Yulang.GeneralLiveCompoundPoint316
open GeneralDictionaryJournalRefinement228Source (root roles snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry boundary_checked initialState)
open GeneralLiveCompoundInstall316 (installed initial_reachable reachable packet_iff)
open GeneralLiveCompoundRoot316 (effect)
open GeneralDictionaryJournalRefinement228Reobserve (looseExtended)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev allocated := installed.core.erased.current.context.state.allocated
noncomputable abbrev reserved := installed.core.erased.current.context.state.reserved
noncomputable abbrev ordinary := installed.core.erased.current.context.state.ordinary

theorem loose : installed.core.erased.current.context.state = looseExtended allocated reserved ordinary := rfl

noncomputable abbrev point := GeneralDictionaryVersionedReobserve233.result allocated reserved ordinary loose

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root installed point :=
  GeneralNominalVersionedMixedKernel234.old_step
    (GeneralDictionaryVersionedReobserve233.step rfl allocated reserved ordinary loose registry root)

theorem point_reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root point := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initial,.tail path step⟩

theorem install_models (m : Assignment) : Models installed m ↔ Models GeneralDictionaryCompoundFrame238.installed m := by
  have forward := GeneralNominalVersionedMixedCommon235.installation_models_iff
    (effect := effect) (model := m) boundary_checked initial_reachable rfl rfl
  have backward := GeneralNominalVersionedMixedCommon235.installation_models_iff
    (effect := GeneralDictionaryCompoundFrame238.effect) (model := m)
    ⟨rfl,GeneralDictionaryCompoundSource238.checked⟩ GeneralDictionaryCompoundStep238.initial_reachable rfl rfl
  change Models (GeneralNominalVersionedInstall232.install initialState effect) m ↔
    Models (GeneralNominalVersionedInstall232.install GeneralDictionaryCompoundFrame238.before GeneralDictionaryCompoundFrame238.effect) m
  rw [GeneralNominalVersionedInstall232.install_models (effect := effect) rfl,forward,
    GeneralNominalVersionedInstall232.install_models (effect := GeneralDictionaryCompoundFrame238.effect) rfl,backward]
  constructor
  · rintro ⟨model,packet,live⟩
    exact ⟨model,(packet_iff m).mp packet,live⟩
  · rintro ⟨model,packet,live⟩
    exact ⟨model,(packet_iff m).mpr packet,live⟩

theorem point_models (m : Assignment) : Models point m ↔ Models GeneralDictionaryCompoundPoint238.point m := by
  rw [GeneralDictionaryVersionedReobserve233.models_iff rfl allocated reserved ordinary loose,
    GeneralDictionaryCompoundPoint238.models_iff,install_models]

end Yulang.GeneralLiveCompoundPoint316
