import Yulang.GeneralRebaseCompilerInputs269
import Yulang.GeneralRebaseCompilerFixture268

set_option maxRecDepth 28000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseEnhancedPipeline269
open GeneralDictionaryCompoundFrame238 (before prepared installed)
open GeneralDictionaryCompoundSource238 (sourceRegistry declaration)
open GeneralDictionaryCompoundPacket238 (packet)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralRebaseDiagnosticFixture268 (checked)
open GeneralRebaseCompilerFixture268 (replies certified)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseDiagnosticCompiler268 (compile)
open GeneralRebaseCompilerInputs269 (Inputs Checked enhance)
open GeneralRebaseConsensusDiagnostic268 (run)
open CommonRoleOutermostResolver (Frontier)

def extra : Inputs before := ⟨fun _ _ => none,fun _ _ => none,fun _ => none⟩

theorem extra_cert : Checked before extra := ⟨fun _ _ => True.intro,fun _ _ => True.intro,fun _ => True.intro⟩

noncomputable def compiled :=
 compile sourceRegistry before root root checked (enhance before extra replies)

theorem rootKnown : compiled.rootPending = some false := by decide +kernel
theorem cycleClear : GeneralRebaseDiagnosticData268.k2 compiled = some false := by decide +kernel
theorem inspectionClear : compiled.inspection = some false := by decide +kernel
theorem overlaysClear : GeneralRebaseDiagnosticV8268.conflicts compiled = some false := by decide +kernel
theorem outputClear : compiled.outputConflict declaration.id = some false := by decide +kernel

theorem verdict : run compiled = some (.selected declaration.id (GeneralNominalVersionedFrame231.children packet)) := by
 have survivor : compiled.survivors = .unique (declaration.id,GeneralNominalVersionedFrame231.children packet) :=
   GeneralRebaseHeadProbeFixture267.verified_choice
 simp only [run,overlaysClear,GeneralRebaseDiagnosticV6268.run,rootKnown,cycleClear,inspectionClear,
   GeneralRebaseDiagnosticV6268.known,survivor]
 change (match compiled.outputConflict declaration.id with
 | none => none
 | some true => some Frontier.rejected
 | some false => some (Frontier.selected declaration.id (GeneralNominalVersionedFrame231.children packet))) = _
 rw [outputClear]

theorem selected :
 B4TargetV8.Local (Boundary roles) sourceRegistry before root
   (.selected declaration.id (GeneralNominalVersionedFrame231.children packet)) :=
 GeneralRebaseCompilerInputs269.run_sound sourceRegistry before root root checked
   GeneralDictionaryCompoundStep238.initial_reachable .root prepared.1 extra extra_cert replies certified verdict

theorem guard : GeneralRebaseSourceSelect267.Guard sourceRegistry before root declaration.id := by
 obtain ⟨v7,clearSharing⟩ := B4TargetV8.selected_iff.mp selected
 obtain ⟨v6,clearMerged⟩ := B4TargetV7.selected_iff.mp v7
 cases v6 with
 | selected safe _ output => exact ⟨safe,output,clearMerged,clearSharing⟩

theorem actual_install :
 (Boundary roles).Step sourceRegistry root before installed ∧
 ∃ model, GeneralNominalVersionedJournal232.Models installed model := by
 let effect := GeneralDictionaryCompoundFrame238.effect
 obtain ⟨derived,reg,ctx,same,step,models⟩ :=
   GeneralRebaseExecutableInstall267.source_step sourceRegistry before root root checked
    GeneralDictionaryCompoundStep238.initial_reachable .root prepared.1
    GeneralRebaseHeadProbeFixture267.certifiedCase GeneralRebaseHeadProbeFixture267.certifiedCase_honest
    GeneralRebaseInstallFixture267.actual_select guard (fun derived reg ctx same => by
      cases GeneralRebaseSourceInstall267.effect_ext derived effect reg ctx same
      exact ⟨GeneralDictionaryCompoundVersionedModel238.extended,GeneralRebaseProspectiveFixture264.residual⟩)
 cases GeneralRebaseSourceInstall267.effect_ext derived effect reg ctx same
 exact ⟨step,models⟩

end Yulang.GeneralRebaseEnhancedPipeline269
