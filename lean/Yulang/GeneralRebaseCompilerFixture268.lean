import Yulang.GeneralRebaseDiagnosticCompiler268
import Yulang.GeneralRebaseIntegratedFixture268

set_option maxRecDepth 26000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseCompilerFixture268
open GeneralDictionaryCompoundFrame238 (before prepared class_effects)
open GeneralDictionaryCompoundPacket238 (plan packet ready)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry declaration)
open GeneralDictionaryJournalRefinement228Source (root roles context)
open GeneralDictionaryOptionalEnable229 (sourceForm raw_edge_decreases)
open GeneralDictionaryCompoundVersionedModel238 (extended initial_model)
open GeneralDictionaryCompoundVersionedPacket238 (head_model packet_holds)
open GeneralRebaseDiagnosticFixture268 (checked)
open GeneralRebaseDiagnosticCompiler268 (Replies Certified compile)
open GeneralRebaseDiagnosticData268 (Inputs)
open GeneralRebaseCandidateK2Source268 (focusPlans)
open GeneralRebasePartialBool268 (Reflect)
open GeneralRebaseInspectionChecks268 (prepared_formula)
open GeneralRebaseConsensusDiagnostic268 (run)
open GeneralNominalVersionedDiagnostic232 (head_equations)

def raw : GeneralRebaseRawK2Probe268.Probes before.core.erased.current.context.state :=
 ⟨fun a b => if (sourceForm b.val).rank < (sourceForm a.val).rank then none else some false,none⟩

theorem raw_sound : GeneralRebaseRawK2Probe268.Sound _ raw := by
 constructor
 · intro a b
   change Reflect (GeneralNominalMixedRecurrence.Edge _ a b)
     (if (sourceForm b.val).rank < (sourceForm a.val).rank then none else some false)
   split
   · trivial
   · rename_i no
     exact fun edge => no (raw_edge_decreases edge)
 · exact True.intro

def replies : Replies before :=
 ⟨some true,raw,fun _ => some false,fun _ _ => some true,fun _ => some true,fun _ _ => none,
   fun _ => none,fun _ => some true,fun _ => some true,some true,fun _ _ => none,fun _ _ => none⟩

theorem only_plan {other} (listed : other ∈ focusPlans sourceRegistry before root root checked) :
 other = plan := by
 have found : other ∈ GeneralRebaseCandidateFixture267.inferred :=
   ((GeneralRebaseCandidateK2Source268.focusPlans_exact ..).mp listed).1
 rw [GeneralRebaseCandidateFixture267.inferred_exact] at found
 exact List.mem_singleton.mp found

theorem certified : Certified sourceRegistry before root root checked replies := by
 constructor
 · exact prepared.1
 · exact raw_sound
 · exact GeneralDictionaryCompoundStep238.acyclic
 · intro d member bounds loc
   cases List.mem_singleton.mp member
   exact ((prepared_formula registry context root declaration bounds loc).mp prepared).2.2.2.2
 · intro p listed
   cases only_plan listed
   exact ⟨extended,head_model⟩
 · intro; intros; exact True.intro
 · intro; intros; exact True.intro
 · intro p listed
   cases only_plan listed
   exact ⟨extended,initial_model,ready,head_equations packet_holds,class_effects⟩
 · intro p listed
   cases only_plan listed
   exact ⟨extended,initial_model,GeneralNominalVersionedHeadSharing232.schema_holds plan extended
     (head_equations packet_holds).2.2⟩
 · exact ⟨extended,initial_model⟩
 · intro; intros; exact True.intro
 · intro; intros; exact True.intro

noncomputable def input : Inputs (GeneralSourceDictionaries.Occurrence roles) :=
 compile sourceRegistry before root root checked replies

theorem rootClear : input.rootK2 = some false := by decide +kernel
theorem candidateClear : input.candidateK2 = some false := by decide +kernel
theorem inspectionClear : input.inspection = some false := by decide +kernel
theorem mergedClear : input.mergedConflict = some false := by decide +kernel
theorem shareClear : input.sharingConflict = some false := by decide +kernel
theorem outputClear : input.outputConflict declaration.id = some false := by decide +kernel

theorem actual_run : run input = some (.selected declaration.id (GeneralNominalVersionedFrame231.children packet)) := by
 have survivor : input.survivors = .unique (declaration.id,GeneralNominalVersionedFrame231.children packet) :=
   GeneralRebaseHeadProbeFixture267.verified_choice
 have rootKnown : input.rootPending = some false := by decide +kernel
 have noK2 : GeneralRebaseDiagnosticData268.k2 input = some false := by
   simp [GeneralRebaseDiagnosticData268.k2,rootClear,candidateClear,GeneralRebasePartialBool268.either]
 have noConflict : GeneralRebaseDiagnosticV8268.conflicts input = some false := by
   simp [GeneralRebaseDiagnosticV8268.conflicts,shareClear,mergedClear,GeneralRebasePartialBool268.either]
 simp only [run,noConflict,GeneralRebaseDiagnosticV6268.run,rootKnown,noK2,inspectionClear,
   GeneralRebaseDiagnosticV6268.known,survivor]
 change (match input.outputConflict declaration.id with
 | none => none
 | some true => some CommonRoleOutermostResolver.Frontier.rejected
 | some false => some (CommonRoleOutermostResolver.Frontier.selected declaration.id (GeneralNominalVersionedFrame231.children packet))) = _
 rw [outputClear]

/-- Uses independently proved semantic inputs, not an assumed local verdict
or supplied whole-predicate answers for the six local diagnostics. -/
theorem actual_selected :
 B4TargetV8.Local (GeneralRebaseSourceSurvivor267.Boundary roles) sourceRegistry before root
   (.selected declaration.id (GeneralNominalVersionedFrame231.children packet)) :=
 GeneralRebaseDiagnosticCompiler268.sound sourceRegistry before root root checked
   GeneralDictionaryCompoundStep238.initial_reachable .root prepared.1 replies certified actual_run

theorem compiled_guard : GeneralRebaseSourceSelect267.Guard sourceRegistry before root declaration.id := by
 obtain ⟨v7,clearSharing⟩ := B4TargetV8.selected_iff.mp actual_selected
 obtain ⟨v6,clearMerged⟩ := B4TargetV7.selected_iff.mp v7
 cases v6 with
 | selected safe _ output => exact ⟨safe,output,clearMerged,clearSharing⟩

/-- Current-source candidate selection plus the compiled diagnostic, with
separate joint-model and novelty certificates, produces the genuine step. -/
theorem actual_generated_install :
 (GeneralRebaseSourceSurvivor267.Boundary roles).Step sourceRegistry root before GeneralDictionaryCompoundFrame238.installed ∧
 ∃ model, GeneralNominalVersionedJournal232.Models GeneralDictionaryCompoundFrame238.installed model := by
 let effect := GeneralDictionaryCompoundFrame238.effect
 obtain ⟨derived,registry_eq,atState,same,operational,hasModel⟩ :=
   GeneralRebaseExecutableInstall267.source_step sourceRegistry before root root checked
     GeneralDictionaryCompoundStep238.initial_reachable .root prepared.1
     GeneralRebaseHeadProbeFixture267.certifiedCase GeneralRebaseHeadProbeFixture267.certifiedCase_honest
     GeneralRebaseInstallFixture267.actual_select compiled_guard
     (fun derived reg context planEq => by
       cases GeneralRebaseSourceInstall267.effect_ext derived effect reg context planEq
       exact ⟨extended,GeneralRebaseProspectiveFixture264.residual⟩)
 cases GeneralRebaseSourceInstall267.effect_ext derived effect registry_eq atState same
 exact ⟨operational,hasModel⟩

end Yulang.GeneralRebaseCompilerFixture268
