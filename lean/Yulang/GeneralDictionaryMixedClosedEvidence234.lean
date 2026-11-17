import Yulang.GeneralDictionaryMixedClosedFrame234
import Yulang.GeneralDictionaryMixedClosedTransport234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedClosedEvidence234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedClosedPlan234
open GeneralDictionaryMixedClosedStep234 (next models_iff)
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)

theorem old_plan : oldPlan = GeneralNominalVersionedInstallation231.replayPlan
    GeneralDictionaryVersionedSecondInstall233.plan := rfl

theorem packet {model : Assignment} (valid : Models next model) :
    GeneralNominalVersionedPlans231.Holds plan model := by
  apply GeneralDictionaryMixedClosedTransport234.holds valid.1.1
  rw [old_plan]
  exact GeneralNominalVersionedInstalledEvidence233.replay_holds ((models_iff model).mp valid)

theorem evidence {model : Assignment} (valid : Models next model) :
    GeneralNominalVersionedEvidence231.Evidence registry next.core model root (.node declaration.id []) :=
  GeneralDictionaryMixedClosedFrame234.evidence (packet valid)

theorem unique {model : Assignment} (valid : Models next model) :
    GeneralNominalVersionedCandidates231.Unique registry next.core.erased.current.context root declaration.id [] :=
  GeneralDictionaryMixedClosedFrame234.unique (packet valid)

theorem inhabited_evidence : ∃ model, Models next model ∧
    GeneralNominalVersionedEvidence231.Evidence registry next.core model root (.node declaration.id []) := by
  obtain ⟨model,valid⟩ := GeneralDictionaryMixedClosedStep234.nonempty_models
  exact ⟨model,valid,evidence valid⟩

end Yulang.GeneralDictionaryMixedClosedEvidence234
