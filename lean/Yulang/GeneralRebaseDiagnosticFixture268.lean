import Yulang.GeneralRebaseDiagnosticSource268
import Yulang.GeneralRebaseInstallFixture267

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralRebaseDiagnosticFixture268
open GeneralRebaseDiagnosticSource268 (Probes Sound prepare)
open GeneralRebaseDiagnosticV8268 (run)
open GeneralDictionaryCompoundFrame238 (before prepared)
open GeneralDictionaryCompoundPacket238 (packet)
open GeneralDictionaryCompoundSource238 (sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralRebaseHeadProbeFixture267 (certifiedCase certifiedCase_honest verified_choice)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralNominalVersionedFrame231 (children)

theorem checked : (Boundary roles).Checked sourceRegistry := ⟨rfl,GeneralDictionaryCompoundSource238.checked⟩

def probes : Probes :=
 ⟨some false,some false,some false,fun key => if key = declaration.id then some false else none,
  some false,some false⟩

theorem sound : Sound sourceRegistry before root probes := by
 have facts := GeneralRebaseInstallFixture267.guard
 refine ⟨facts.safe.2.1,facts.safe.2.2.1,facts.safe.2.2.2,?_,facts.clearMerged,facts.clearSharing⟩
 intro key
 by_cases equality : key = declaration.id
 · cases equality
   exact facts.clearOutput
 · simp [probes,equality,GeneralRebasePartialBool268.Reflect]

noncomputable def input := prepare sourceRegistry before root root checked certifiedCase probes

theorem pendingGate : input.rootPending = some false := by decide +kernel

theorem actual_run : run input = some (.selected declaration.id (children packet)) := by
 have choice : input.survivors = .unique (declaration.id,children packet) := verified_choice
 have gates : GeneralRebaseDiagnosticV8268.conflicts input = some false := rfl
 have cycles : GeneralRebaseDiagnosticData268.k2 input = some false := rfl
 have inspected : input.inspection = some false := rfl
 have output : input.outputConflict declaration.id = some false := by simp [input,prepare,probes]
 simp only [run,gates,GeneralRebaseDiagnosticV6268.run,pendingGate,cycles,inspected,
   GeneralRebaseDiagnosticV6268.known,choice,output]

/-- Actual Local verdict regenerated from source and certified primitive
facts, with no caller-supplied candidate list or preassigned decision. -/
theorem independently_selected :
 B4TargetV8.Local (Boundary roles) sourceRegistry before root (.selected declaration.id (children packet)) :=
 GeneralRebaseDiagnosticV8268.sound _ _ _ _ input
   (GeneralRebaseDiagnosticSource268.valid sourceRegistry before root root checked
      GeneralDictionaryCompoundStep238.initial_reachable .root prepared.1 certifiedCase
      certifiedCase_honest probes sound) actual_run

end Yulang.GeneralRebaseDiagnosticFixture268
