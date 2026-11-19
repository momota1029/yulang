import Yulang.GeneralRebaseExecutableInstall267
import Yulang.GeneralRebaseHeadProbeFixture267

set_option maxRecDepth 12000
set_option maxHeartbeats 3400000
namespace Yulang.GeneralRebaseInstallFixture267
open GeneralDictionaryCompoundFrame238 (before effect installed)
open GeneralDictionaryCompoundPacket238 (plan packet)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralRebaseHeadProbeFixture267 (entries entries_exact certifiedCase certifiedCase_honest verified_choice)
open GeneralRebaseExecutableInstall267 (select)
open GeneralRebaseInstallChecks267 (choice edgesRecorded)
open GeneralNominalVersionedFrame231 (children)

theorem picked : GeneralRebasePickPlan267.pick certifiedCase entries (declaration.id,children packet) = some plan := by
 have matched : GeneralRebasePickPlan267.matching certifiedCase (declaration.id,children packet) plan = true :=
   (GeneralRebasePickPlan267.matches_exact ..).mpr ⟨rfl,rfl⟩
 rw [entries_exact]
 unfold GeneralRebasePickPlan267.pick
 simp [matched]

theorem history : choice before.core.erased.current packet = true := rfl

theorem missing : edgesRecorded before.core.erased.current plan = false := by
 decide +kernel

theorem actual_select : select before certifiedCase entries = some plan :=
 GeneralRebaseExecutableInstall267.select_with_witness before certifiedCase entries verified_choice picked history missing

theorem guard : GeneralRebaseSourceSelect267.Guard sourceRegistry before root declaration.id := by
 obtain ⟨v7,clearSharing⟩ := B4TargetV8.selected_iff.mp GeneralRebaseProspectiveFixture264.selected
 obtain ⟨v6,clearMerged⟩ := B4TargetV7.selected_iff.mp v7
 cases v6 with
 | selected safe _ output => exact ⟨safe,output,clearMerged,clearSharing⟩

/-- The start state is the actual source journal. The Plan is computed
from it, with no stored edge list, and then certified using the fixture's
separate head and joint-model witnesses. -/
theorem actual_generated_install :
 (GeneralRebaseSourceSurvivor267.Boundary roles).Step sourceRegistry root before installed ∧
 ∃ model, GeneralNominalVersionedJournal232.Models installed model := by
 have checked : (GeneralRebaseSourceSurvivor267.Boundary roles).Checked sourceRegistry :=
   ⟨rfl,GeneralDictionaryCompoundSource238.checked⟩
 obtain ⟨derived,registry_eq,atState,same,operational,hasModel⟩ :=
   GeneralRebaseExecutableInstall267.source_step sourceRegistry before root root checked
     GeneralDictionaryCompoundStep238.initial_reachable .root
     GeneralDictionaryCompoundSource238.source.metadata certifiedCase certifiedCase_honest actual_select guard
     (fun derived reg context planEq => by
       cases GeneralRebaseSourceInstall267.effect_ext derived effect reg context planEq
       exact ⟨GeneralDictionaryCompoundVersionedModel238.extended,GeneralRebaseProspectiveFixture264.residual⟩)
 cases GeneralRebaseSourceInstall267.effect_ext derived effect registry_eq atState same
 exact ⟨operational,hasModel⟩

end Yulang.GeneralRebaseInstallFixture267
