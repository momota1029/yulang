import Yulang.GeneralRebaseDisplayWatch284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseOptionalWatch284
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (effect installed)
open GeneralRebaseOptionalOverwrite282 (point_reached)
open GeneralRebaseOptionalDelta283 (oldLo oldHi newLo newHi before_contents after_contents)
open GeneralRebaseWatchValidator284 (Compact Valid high)
open GeneralRebaseWatchValidatorSource284 (candidate)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseActualWatch284 (interpret)
open GeneralRebaseFutureWatch284 (Closed)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralNominalVersionedJournal232 (Models)
open GeneralPresenceDefinitionRewrite244 (Entry)

noncomputable def prior := GeneralRebaseInstallCache283.initial point

theorem prior_valid : GeneralRebaseInstallCache283.Valid prior point :=
  GeneralRebaseInstallCache283.initial_valid (GeneralNominalVersionedMixedSeedLedger237.reachable point_reached)

noncomputable def watch : List Nat := [2,4,oldLo.1,oldHi.1,newLo.1,newHi.1] ++ journalReads installed
noncomputable def saved : Compact := ⟨high 0 prior,watch,prior⟩

theorem old_supported (row : Entry Nat) (inCache : row ∈ prior) :
    GeneralPresenceUsedSupport245.typedReads row.2 ⊆ watch := by
  rcases (before_contents prior_valid row).mp inCache with rfl|rfl
  all_goals
    intro n member
    simp only [oldLo,oldHi,GeneralPresenceUsedSupport245.typedReads,List.mem_append,List.mem_singleton,or_self] at member
    subst n
    exact List.mem_append_left _ (by simp)

theorem prior_good : Valid saved (history point) where
  bound := fun r seen => GeneralRebaseWatchValidator284.high_covers 0 prior r ((prior_valid.content r).mpr seen)
  covers :=
    ⟨fun r seen _ => old_supported r ((prior_valid.content r).mpr seen),
     fun {r} found => (prior_valid.content r).mp found,
     fun r seen _ => (prior_valid.content r).mpr seen⟩
  sorted := prior_valid.increasing

theorem after_closed : Closed watch (history installed) := by
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable point_reached
  have valid := GeneralRebaseInstallCache283.add_valid (effect := effect) prior_valid record rfl
  intro row found _
  rcases (after_contents prior_valid row).mp ((valid.content row).mpr found) with (rfl | rfl) | earlier
  · intro n used
    simp only [newLo,GeneralPresenceUsedSupport245.typedReads,List.mem_append,List.mem_singleton,or_self] at used
    subst n; exact List.mem_append_left _ (by simp)
  · intro n used
    simp only [newHi,GeneralPresenceUsedSupport245.typedReads,List.mem_append,List.mem_singleton,or_self] at used
    subst n; exact List.mem_append_left _ (by simp)
  · exact old_supported row earlier

theorem certified_install :
    ∃ next, candidate saved watch effect = some next ∧
        (∃ b, Models installed (interpret next.kept b)) := by
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable point_reached
  obtain ⟨next,checked⟩ := GeneralRebaseWatchValidatorSource284.passes prior_good record
    (effect := effect) rfl ((GeneralRebaseWatchValidator284.admissible _ _ _).mpr fun _ h => Or.inl h)
    after_closed
  have complete := GeneralRebaseWatchValidatorSource284.candidate_exact prior_good point_reached rfl checked
    (fun {_} req => List.mem_append_right _ req)
  exact ⟨next,checked,complete.mpr ⟨_,GeneralDictionaryVersionedSecondInstall233.installation_models⟩⟩

end Yulang.GeneralRebaseOptionalWatch284
