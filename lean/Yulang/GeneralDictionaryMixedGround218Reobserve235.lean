import Yulang.GeneralDictionaryGroundCopy218Reobserve
import Yulang.GeneralNominalVersionedMixedKernel234
import Yulang.GeneralNominalVersionedMixedKernelCache234
set_option backward.isDefEq.respectTransparency false
/-! Source-derived improving reobservation on the genuine mixed journal.
The hypotheses identify the concrete eight-slot source and current snapshot;
no current model equivalence or desired dictionary evidence is assumed. -/
namespace Yulang.GeneralDictionaryMixedGround218Reobserve235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Reobserve
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
variable {state : State roles}

def revision (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :=
  revisionFor state.core.erased.current allocated reserved ordinary same

def result (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) : State roles :=
  GeneralNominalVersionedRefresh232.reobserve state (revision allocated reserved ordinary same)

theorem certificate (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    GeneralNominalCenteredHeadMatStepRefresh.Reobserve state.legacy (revision allocated reserved ordinary same) :=
  revision_certificate state.legacy source allocated reserved ordinary same

theorem step (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary)
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalVersionedMixedKernel234.Step registry root state (result allocated reserved ordinary same) :=
  ⟨root,.root,.administrative (.reobserve root _
    ⟨(certificate source allocated reserved ordinary same).raw,GeneralNominalVersionedMixedObservations233.legacy_cache (certificate source allocated reserved ordinary same).cache⟩
    (revision_improves state.core.erased.current allocated reserved ordinary same))⟩

theorem models_iff (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) (model : Assignment) :
    Models (result allocated reserved ordinary same) model ↔ Models state model :=
  GeneralNominalVersionedRefresh232.reobserve_models (certificate source allocated reserved ordinary same) model

theorem nonempty (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary)
    (inhabited : ∃ model, Models state model) : ∃ model, Models (result allocated reserved ordinary same) model := by
  obtain ⟨model,valid⟩ := inhabited
  exact ⟨model,(models_iff source allocated reserved ordinary same model).mpr valid⟩

theorem current_snapshot (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    (result allocated reserved ordinary same).core.erased.current.context.state = pointExtended allocated reserved ordinary :=
  revision_snapshot state.core.erased.current allocated reserved ordinary same

theorem plans_unchanged (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    (result allocated reserved ordinary same).plans = state.plans := rfl

theorem effects_unchanged (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    (result allocated reserved ordinary same).effects = state.effects := rfl

theorem source_unchanged (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    (result allocated reserved ordinary same).core.erased.source = state.core.erased.source := rfl

theorem raw_sites_unchanged (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    (result allocated reserved ordinary same).core.erased.current.sites = state.core.erased.current.sites := rfl

theorem centered_sites_unchanged (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    (result allocated reserved ordinary same).core.sites = state.core.sites := rfl

end Yulang.GeneralDictionaryMixedGround218Reobserve235
