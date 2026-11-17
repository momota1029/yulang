import Yulang.GeneralDictionaryVersionedCompletion231
import Yulang.GeneralNominalVersionedInstallation231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedReconstruction231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedCompletion231
open GeneralNominalCommonBridge (Assignment)

noncomputable def replayed := GeneralNominalVersionedInstallation231.replayPlan currentPlan

/-- A concrete data-level context reconstruction. Calling Journal.refresh here
is only its state constructor: no old Refresh certificate or operational Step
is asserted. The successor installer still has to integrate this transformer. -/
noncomputable def reconstructed :=
  GeneralNominalCenteredHeadMatStepJournal.refresh after replayed.packet.context

theorem models_iff (m : Assignment) :
    GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m ↔ InstallationModels m := by
  unfold GeneralNominalCenteredHeadMatStepJournal.Models InstallationModels
  change (GeneralNominalState.Models replayed.packet.context.state m ∧ _) ↔ _
  unfold replayed
  rw [GeneralNominalVersionedInstallation231.replay_private_models,GeneralNominalVersionedPlans231.private_models_iff]
  constructor
  · rintro ⟨⟨raw,ordinary⟩,source,rawSites,sites,plans,effects⟩
    refine ⟨⟨raw,source,rawSites,sites,plans,?_⟩,?_⟩
    · intro effect member
      have pair := effects effect member
      exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := after.core) (after := reconstructed.core)
          (fun _ h => h) (fun _ h => h)) pair.2⟩
    · have merges := ordinary.2.1
      rw [GeneralDictionaryUpper230Current.bindings_exact] at merges
      exact merges
  · rintro ⟨⟨raw,source,rawSites,sites,plans,effects⟩,new⟩
    refine ⟨⟨raw,GeneralDictionaryVersionedCompletion231.ordinary new⟩,source,rawSites,sites,plans,?_⟩
    intro effect member
    have pair := effects effect member
    exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := reconstructed.core) (after := after.core)
        (fun _ h => h) (fun _ h => h)) pair.2⟩

theorem inhabited : ∃ m, GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m := by
  obtain ⟨m,valid⟩ := GeneralDictionaryVersionedCompletion231.inhabited
  exact ⟨m,(models_iff m).mpr valid⟩

theorem packet_holds (valid : GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m) :
    GeneralNominalVersionedPlans231.Holds replayed m :=
  (GeneralNominalVersionedInstallation231.replay_holds_iff currentPlan m).mpr
    (GeneralDictionaryVersionedCompletion231.packet_holds ((models_iff m).mp valid))

theorem source_preserved (slot : Fin extendedSnapshot.base.slots) :
    reconstructed.core.erased.current.context.state.base.source slot = extendedSnapshot.base.source slot := rfl

theorem centers_preserved : reconstructed.core.sites = after.core.sites := rfl

theorem historical_plans_preserved : reconstructed.core.plans = after.core.plans := rfl

theorem historical_effects_preserved : reconstructed.effects = after.effects := rfl

theorem children_empty : GeneralNominalVersionedFrame231.children replayed.packet = [] := by
  unfold replayed
  rw [GeneralNominalVersionedInstallation231.replay_children]
  exact GeneralDictionaryVersionedEvidence231.children_empty

end Yulang.GeneralDictionaryVersionedReconstruction231
