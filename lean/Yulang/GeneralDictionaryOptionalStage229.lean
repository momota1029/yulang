import Yulang.GeneralDictionaryOptionalInstall229
import Yulang.GeneralDictionaryOptionalCurrent229

namespace Yulang.GeneralDictionaryOptionalStage229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralNominalCenteredHeadMatStepJournal

abbrev allocated := packet.privateContext.state.allocated
abbrev reserved := packet.privateContext.state.reserved
abbrev ordinary := packet.privateContext.state.ordinary

theorem installed_snapshot : installed.core.erased.current.context.state =
    looseExtended allocated reserved ordinary := rfl

noncomputable def revision : GeneralNominalReobservationSteps.Revision installed.core.erased.current :=
  revisionFor installed.core.erased.current allocated reserved ordinary installed_snapshot
noncomputable def stage := change installed revision.result

theorem certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve installed revision :=
  revision_certificate installed rfl allocated reserved ordinary installed_snapshot

theorem step : GeneralDictionaryDefaultKernel208.Step registry root installed stage :=
  revision_step installed rfl allocated reserved ordinary installed_snapshot registry root

theorem stage_models (m : GeneralNominalCommonBridge.Assignment) : Models stage m ↔ Models installed m :=
  GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate

theorem stage_model : Models stage model := (stage_models model).mpr installed_model

theorem context_eq : stage.core.erased.current.context =
    GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary :=
  congrArg (fun data : GeneralNominalState.State => (⟨data,interpretation⟩ : GeneralNominalCandidates.Context))
    (revision_snapshot installed.core.erased.current allocated reserved ordinary installed_snapshot)

theorem raw_sites : stage.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := rfl
theorem centers : stage.core.sites = [GeneralNominalCenters.rootSite snapshot.seed root] := rfl

theorem no_instance : ¬ GeneralDictionaryTotalEvidence206.Instance registry stage.core model root key children :=
  GeneralDictionaryOptionalCurrent229.no_instance allocated reserved ordinary context_eq raw_sites centers
    model rfl lower_value

/-- A complete model and a real certified reobservation are available. This
statement deliberately does not assert initial reachability or Stable/Local. -/
theorem certified_obstruction :
    Models installed model ∧ GeneralDictionaryDefaultKernel208.Step registry root installed stage ∧
    Models stage model ∧ ¬ GeneralDictionaryTotalEvidence206.Instance registry stage.core model root key children :=
  ⟨installed_model,step,stage_model,no_instance⟩
end Yulang.GeneralDictionaryOptionalStage229
