import Yulang.GeneralNominalVersionedMixedEmbedding234
import Yulang.GeneralDictionaryVersionedUpperRefresh233
import Yulang.GeneralDictionaryMixedClosedRefresh234
import Yulang.GeneralDictionaryVersionedSecondStep233
import Yulang.GeneralDictionaryVersionedSecondStable233
set_option backward.isDefEq.respectTransparency false
/-! Actual new-cache learning from the genuine source trace. The old endpoint
is stable only in Kernel232; the mixed-cache kernel has a real next step. -/
namespace Yulang.GeneralDictionaryMixedClosedStep234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryMixedClosedSnapshot234 (extendedContext)
open GeneralDictionaryVersionedUpperRefresh233
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedKernel234

noncomputable abbrev next := GeneralNominalVersionedRefresh232.refresh installed extendedContext
noncomputable def mixedCertificate : GeneralNominalVersionedMixedObservations233.Refresh installed extendedContext :=
  GeneralDictionaryMixedClosedRefresh234.certificate

theorem action : At registry installed root next :=
  .refresh root extendedContext mixedCertificate GeneralDictionaryVersionedUpperBase233.hi
    upper_supported upper_unknown ⟨(7 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩

theorem step : Step registry root installed next := ⟨root,.root,action⟩

theorem not_stable : ¬ Stable registry installed root := by
  intro stopped
  exact stopped root .root next action

theorem old_stable : GeneralNominalVersionedKernel232.Stable registry installed root :=
  GeneralDictionaryVersionedSecondStable233.stable

theorem source_reachable :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root next := by
  obtain ⟨first,initial,path⟩ := GeneralDictionaryVersionedSecondStep233.reachable
  exact ⟨first,initial,.tail (old_steps path) step⟩

theorem models_iff (model : GeneralNominalCommonBridge.Assignment) : Models next model ↔ Models installed model :=
  GeneralDictionaryMixedClosedRefresh234.model_preserved model

theorem nonempty_models : ∃ model, Models next model := by
  exact ⟨_,(models_iff _).mpr GeneralDictionaryVersionedSecondInstall233.installed_model⟩

theorem cache : GeneralNominalVersionedMixedKernelCache234.Valid next :=
  GeneralNominalVersionedMixedEmbedding234.source_cache source_reachable

theorem source_preserved : next.core.erased.source = installed.core.erased.source := rfl

theorem plans_preserved : next.plans = installed.plans := rfl

theorem effects_preserved : next.effects = installed.effects := rfl

end Yulang.GeneralDictionaryMixedClosedStep234
