import Yulang.GeneralRebaseTerminalRowTransfer274

set_option maxRecDepth 17000
set_option maxHeartbeats 5100000
namespace Yulang.GeneralRebaseTerminalRowFrame274
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Ordinary HeadModels)
open GeneralRebaseTerminalRowTransfer274 (Invariant ordinary head legacy journal)
open GeneralRebaseTypeOnlyAtoms273 (atomTypeOnly)
open GeneralNominalVersionedInstallation231 (replay_private_models)
open GeneralDictionaryJournalRefinement228Reobserve (extended_models_iff)
open GeneralDictionaryJournalRefinement228Source (snapshot)
open GeneralDictionaryVersionedPointStage233 (point allocated reserved)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralRebaseTerminalPublic274 (first final_legacy_empty)

abbrev oldPlan := GeneralDictionaryOptionalInstall229.plan
noncomputable abbrev newPlan := GeneralDictionaryVersionedSecondInstall233.plan

theorem old_ordinary : Invariant (Ordinary oldPlan.packet) := by
 apply ordinary oldPlan <;> decide +kernel

theorem new_ordinary : Invariant (Ordinary newPlan.packet) := by
 apply ordinary newPlan <;> decide +kernel

theorem source : Invariant (GeneralNominalState.Models snapshot) :=
 fun same => GeneralRebaseCompoundRows273.source same

theorem first_raw_exact (m : Assignment) :
 GeneralNominalState.Models first.core.erased.current.context.state m ↔
 GeneralNominalState.Models snapshot m ∧ Ordinary oldPlan.packet m :=
 (replay_private_models oldPlan m).trans (GeneralNominalVersionedPlans231.private_models_iff oldPlan.packet m)

theorem point_raw_exact (m : Assignment) :
 GeneralNominalState.Models point.core.erased.current.context.state m ↔
 GeneralNominalState.Models snapshot m ∧ Ordinary oldPlan.packet m :=
 (extended_models_iff allocated reserved GeneralDictionaryVersionedPointStage233.ordinary m).trans
   (first_raw_exact m)

theorem terminal_raw_exact (m : Assignment) :
 GeneralNominalState.Models installed.core.erased.current.context.state m ↔
 GeneralNominalState.Models snapshot m ∧ Ordinary oldPlan.packet m ∧ Ordinary newPlan.packet m := by
 change GeneralNominalState.Models (GeneralNominalVersionedInstallation231.replayPlan newPlan).packet.context.state m ↔ _
 rw [replay_private_models,GeneralNominalVersionedPlans231.private_models_iff]
 change (GeneralNominalState.Models point.core.erased.current.context.state m ∧ _) ↔ _
 rw [point_raw_exact,and_assoc]

theorem point_raw : Invariant (GeneralNominalState.Models point.core.erased.current.context.state) :=
 fun {a b} same => (point_raw_exact a).trans ((and_congr (source same) (old_ordinary same)).trans (point_raw_exact b).symm)

theorem terminal_raw : Invariant (GeneralNominalState.Models installed.core.erased.current.context.state) :=
 fun {a b} same => (terminal_raw_exact a).trans
  ((and_congr (source same) (and_congr (old_ordinary same) (new_ordinary same))).trans (terminal_raw_exact b).symm)

theorem old_head : Invariant (HeadModels oldPlan.packet) := head oldPlan source old_ordinary

theorem new_head : Invariant (HeadModels newPlan.packet) := head newPlan point_raw new_ordinary

theorem terminal_row_free : Invariant (Models installed) := by
 apply journal installed (legacy installed final_legacy_empty terminal_raw source)
 · intro p present
   change p ∈ [newPlan,oldPlan] at present
   rcases List.mem_cons.mp present with rfl | old
   · exact new_head
   · cases List.mem_singleton.mp old
     exact old_head
 · intro e present
   change e ∈ [GeneralDictionaryVersionedSecondInstall233.effect,GeneralDictionaryVersionedInitialFrame233.effect] at present
   rcases List.mem_cons.mp present with rfl | old
   · exact new_head
   · cases List.mem_singleton.mp old
     exact old_head

end Yulang.GeneralRebaseTerminalRowFrame274
