import Yulang.GeneralPositiveForkScope309
import Yulang.GeneralNominalVersionedMixedEvidenceReduction235

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 15500000
namespace Yulang.GeneralPositiveForkCurrentSoundness309
open GeneralPositiveForkSource309 (root registry compiled checked)
open GeneralPositiveForkInstall309 (after reachable inhabited)
open GeneralPositiveForkNodes309
open GeneralPositiveForkSelection309 (holds classes ready unique actual_pick)
open GeneralPositiveForkEvidence309 (alias_identity payload)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedCurrentCandidate235 (Current source_installable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedKernel234 (Installable AlternativesSafe)
open GeneralNominalVersionedCycles232 (Safe)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDeclarationExamples (roles)
open CommonRoleOutermostResolver (All₂)

theorem occurrence (n : Node) : (plan n).packet.site.occurrence = focus n :=
  (current_frame n).occurrence_eq

def effect (n : Node) : Effect roles :=
  ⟨compiled,after.core,plan n,(occurrence n).symm ▸ current_frame n,
    (occurrence n).symm ▸ ((child_list n).symm ▸ unique n),
    (occurrence n).symm ▸ ready n⟩

theorem common (n : Node) (m : Assignment) (valid : Models after m) :
    GeneralNominalVersionedInstall232.InstallationModels after (effect n) m := by
  apply (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ reachable rfl rfl).mpr
  refine ⟨valid,holds n m valid,?_⟩
  change GeneralNominalVersionedEffects231.ClassEffects after.core (plan n).packet.site.occurrence (plan n) m
  rw [occurrence n]
  exact classes n m valid

theorem compatible (n : Node) :
    GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current (plan n).packet := by
  intro p member aliased
  change p ∈ [GeneralPositiveForkPlan309.packet] at member
  cases List.mem_singleton.mp member
  have same := alias_identity aliased
  cases n with
  | parent => rfl
  | low => exact False.elim (GeneralPositiveForkLeafFrame309.invocations .low same)
  | high => exact False.elim (GeneralPositiveForkLeafFrame309.invocations .high same)

theorem positions (n : Node) : Safe after (plan n) := by
  refine ⟨?_,fun _ _ => GeneralRebaseDisplaySafety276.semantic inhabited _⟩
  cases n <;> decide +kernel

theorem alternatives (n : Node) : AlternativesSafe compiled after (plan n).input := by
  intro candidate _ frame
  rw [exact_frame n frame]
  exact positions n

theorem current (n : Node) : Current compiled after (focus n) (effect n) := by
  refine ⟨rfl,rfl,occurrence n,?_,compatible n,positions n,alternatives n,⟨_,common n _ inhabited⟩⟩
  exact GeneralNominalVersionedMixedReady235.materialized reachable (current_frame n)

theorem installable (n : Node) : Installable compiled after (effect n) :=
  by exact source_installable (current n) reachable (actual_pick n)

theorem stable_sound_at :
    B4SkeletonV8.EvidenceAt (boundary roles) registry after root := by
  intro m valid f k kids ds hit stable _ chosen childProof
  have source : ∃ n, f = focus n := by
    rcases hit with rfl|generated
    · exact ⟨.parent,rfl⟩
    · exact generated_nodes _ generated
  obtain ⟨n,rfl⟩ := source
  exact GeneralNominalVersionedMixedStableEvidence235.selected_node stable (installable n)
    (occurrence n) (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp chosen) valid childProof

theorem nonvacuous_existing_bridge (m : Assignment) (valid : Models after m) :
    (boundary roles).Evidence registry after m root payload := by
  have stable := GeneralPositiveForkHalt309.stable
  apply stable_sound_at m valid root 1 [focus .low,focus .high] [.node 2 [],.node 3 []]
    (.inl rfl) (stable .parent) ?_ (actual_pick .parent)
  · exact .cons (GeneralPositiveForkVerified309.evidence_at_low m valid)
      (.cons (GeneralPositiveForkVerified309.evidence_at_high m valid) .nil)
  · intro child here
    rcases List.mem_cons.mp here with rfl|last
    · exact stable .low
    · cases List.mem_singleton.mp last
      exact stable .high

end Yulang.GeneralPositiveForkCurrentSoundness309
