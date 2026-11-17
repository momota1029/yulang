import Yulang.GeneralDictionaryMixedUpperFrame234
import Yulang.GeneralDictionaryMixedUpperTransport234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedUpperEvidence234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedUpperPlan234
open GeneralDictionaryMixedUpperStep234 (next models_iff)
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)

theorem old_plan : oldPlan = GeneralNominalVersionedInstallation231.replayPlan
    GeneralDictionaryVersionedSecondInstall233.plan := rfl

theorem packet {model : Assignment} (valid : Models next model) :
    GeneralNominalVersionedPlans231.Holds plan model := by
  apply GeneralDictionaryMixedUpperTransport234.holds valid.1.1
  rw [old_plan]
  exact GeneralNominalVersionedInstalledEvidence233.replay_holds ((models_iff model).mp valid)

theorem evidence {model : Assignment} (valid : Models next model) :
    GeneralNominalVersionedEvidence231.Evidence registry next.core model root (.node declaration.id []) :=
  GeneralDictionaryMixedUpperFrame234.evidence (packet valid)

theorem unique {model : Assignment} (valid : Models next model) :
    GeneralNominalVersionedCandidates231.Unique registry next.core.erased.current.context root declaration.id [] :=
  GeneralDictionaryMixedUpperFrame234.unique (packet valid)

theorem inhabited_evidence : ∃ model, Models next model ∧
    GeneralNominalVersionedEvidence231.Evidence registry next.core model root (.node declaration.id []) := by
  obtain ⟨model,valid⟩ := GeneralDictionaryMixedUpperStep234.nonempty_models
  exact ⟨model,valid,evidence valid⟩

end Yulang.GeneralDictionaryMixedUpperEvidence234
