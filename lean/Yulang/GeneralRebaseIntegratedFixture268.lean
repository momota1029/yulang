import Yulang.GeneralRebaseIntegratedDiagnostic268
import Yulang.GeneralRebaseDiagnosticFixture268

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralRebaseIntegratedFixture268
open GeneralDictionaryCompoundFrame238 (before prepared)
open GeneralDictionaryCompoundSource238 (sourceRegistry declaration registry)
open GeneralDictionaryJournalRefinement228Source (root roles context)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseDiagnosticSource268 (Probes Sound prepare)
open GeneralRebaseIntegratedDiagnostic268 (enhance enhance_sound)
open GeneralRebaseDiagnosticV8268 (run)
open GeneralRebaseHeadProbeFixture267 (certifiedCase)
open GeneralRebasePartialBool268 (Reflect)
open GeneralRebaseInspectionChecks268 (Head prepared_formula)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalVersionedCandidates231 (inputs)

def fallback : Probes :=
 { GeneralRebaseDiagnosticFixture268.probes with inspection := none, mergedConflict := none }

theorem fallback_sound : Sound sourceRegistry before root fallback := by
 have orig := GeneralRebaseDiagnosticFixture268.sound
 exact ⟨orig.rootK2,orig.candidateK2,True.intro,orig.outputConflict,True.intro,orig.sharingConflict⟩

noncomputable def probes : Probes :=
 enhance sourceRegistry before root (some true) (fun _ _ => some true) (fun _ _ => none) fallback

theorem sound : Sound sourceRegistry before root probes := by
 apply enhance_sound _ _ _ _ _ _ _ fallback_sound
 · exact prepared.1
 · intro decl member bounds location
   have same : decl = declaration := List.mem_singleton.mp member
   subst decl
   exact ((prepared_formula registry context root declaration bounds location).mp prepared).2.2.2.2
 · intro; intros; exact True.intro

theorem inspection_computed : probes.inspection = some false := by decide +kernel

theorem merged_computed : probes.mergedConflict = some false := by decide +kernel

theorem probes_exact : probes = GeneralRebaseDiagnosticFixture268.probes := by
 have inspect := inspection_computed
 have merged := merged_computed
 simp only [probes,enhance] at inspect merged ⊢
 rw [inspect,merged]
 rfl


theorem computed_run :
 run (prepare sourceRegistry before root root GeneralRebaseDiagnosticFixture268.checked certifiedCase probes) =
 some (.selected declaration.id (GeneralNominalVersionedFrame231.children GeneralDictionaryCompoundPacket238.packet)) := by
 rw [probes_exact]
 exact GeneralRebaseDiagnosticFixture268.actual_run

end Yulang.GeneralRebaseIntegratedFixture268
