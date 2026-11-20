import Yulang.GeneralRebaseRefreshCode298

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseRefreshInstall298
open GeneralDictionaryOutputDepth252 (roles sourceRegistry root initial model plan registry reachable)
open GeneralDictionaryOutputDepthInstall252 (effect installed)
open GeneralRebasePreInstallReplay297 (after candidate source_reachable signs_preserved all_tests)
open GeneralRebaseRefreshCode298 (rawCode)
open GeneralRebaseSignedDepth297 (checked)
open GeneralRebaseOutputDepthSuccessor271 (owner output projected_install initial_view)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralRebaseSourceObserver267 (installAt)
open GeneralRebaseSourceWitnessProgram297 (callbacks)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStep258 (write)
open GeneralRebaseMultiSelection263 (proposal ofPlan)
open GeneralRebaseLocalProgram298 (emit)

abbrev probes := callbacks rawCode.models rawCode.checks

theorem scan_exact : installAt sourceRegistry after root root checked probes = [candidate] := by
  have count : (installAt sourceRegistry after root root checked probes).length = 1 := by decide +kernel
  have each : ∀ p ∈ installAt sourceRegistry after root root checked probes, p = candidate := by
    intro p listed
    have h := (GeneralRebaseInstallCandidates267.scan_exact ..).mp listed
    obtain ⟨_,_,same,_,_,_,_,_⟩ := h
    have member := GeneralRebaseSourceQuestions297.of_focus sourceRegistry after root root checked .root p same
    exact (GeneralRebasePreInstallReplay297.listed_after p).mp member
  generalize eq : installAt sourceRegistry after root root checked probes = xs at count each ⊢
  cases xs with
  | nil => cases count
  | cons item xs =>
    cases xs with
    | nil => exact congrArg (fun p => [p]) (each item (List.mem_cons_self ..))
    | cons next rest => simp at count

theorem actual_effect :
    ∃ e : Effect roles, e.plan = candidate ∧ Installable registry after e ∧ ¬ Committed after e.plan := by
  have head := GeneralRebaseWitnessContracts297.honest rawCode.covered rawCode.observed root .root
  have guards : GeneralRebaseInstallCandidates267.Probes registry after
      (probes.novelty root) (probes.joint root)
      (GeneralRebaseHeadProbe267.atFocus registry after root root (declChecked checked)) :=
    GeneralRebaseSignedObserver297.sound_guards (base := ⟨fun _ p => some
      (GeneralRebaseFiniteWitnessTable297.hit rawCode.models rawCode.checks.head p),
      fun _ _ => false,fun _ _ => false,probes.mergeInputs⟩)
      source_reachable (GeneralRebaseWitnessContracts297.install_coverage rawCode.covered) rawCode.observed.2.1 root .root
  have listed : candidate ∈ installAt sourceRegistry after root root checked probes := scan_exact.symm ▸ List.mem_cons_self ..
  obtain ⟨e,same,_,enabled,fresh⟩ := GeneralRebaseRawInstallScan297.selected_raw source_reachable .root
    GeneralRebaseRefreshSafety298.real_metadata GeneralRebaseRefreshSafety298.safe head guards candidate listed
  exact ⟨e,same,enabled,fresh⟩

theorem models_same {e : Effect roles} (same : e.plan = candidate) (enabled : Installable registry after e)
    (a : GeneralNominalCommonBridge.Assignment) :
    Models (install after e) a ↔ Models installed a := by
  apply (GeneralRebaseSignedModels297.accepted_exact checked source_reachable enabled.registry_eq enabled.snapshot_eq a).symm.trans
  rw [same,all_tests]
  exact GeneralRebaseSignedModels297.accepted_exact (e := effect) checked reachable rfl rfl a

theorem real_step {e : Effect roles} (same : e.plan = candidate)
    (enabled : Installable registry after e) (fresh : ¬ Committed after e.plan) :
    (Boundary roles).Step sourceRegistry root after (install after e) :=
  ⟨_,same.symm ▸ (GeneralNominalSaturationState.Generated.root (root := root) (state := after.core.erased.current)),
    .install e enabled fresh⟩

theorem before_projection : project [owner] [output] initial = project [owner] [output] after :=
  GeneralRebaseSourceProjection264.refresh_stutters [owner] [output] initial _

def projectedProposal := proposal after.core (ofPlan candidate)

theorem writes_all : (write (project [owner] [output] after) projectedProposal).remaining = [] := by
  decide +kernel

theorem project_same {e : Effect roles} (same : e.plan = candidate) (enabled : Installable registry after e) :
    project [owner] [output] (install after e) = project [owner] [output] installed := by
  apply GeneralRebaseStep258.state_ext
  rw [GeneralRebaseSourceInstallProjection264.project_install_current sourceRegistry checked root after source_reachable
      e enabled [owner] [output],same,projected_install]
  exact writes_all

theorem exact_two_steps :
    ∃ e : Effect roles, e.plan = candidate ∧ (Boundary roles).Step sourceRegistry root initial after ∧
      (Boundary roles).Step sourceRegistry root after (install after e) ∧
      project [owner] [output] initial = project [owner] [output] after ∧
      project [owner] [output] (install after e) = project [owner] [output] installed ∧
      (∀ m, Models (install after e) m ↔ Models installed m) := by
  obtain ⟨e,same,yes,fresh⟩ := actual_effect
  exact ⟨e,same,GeneralRebasePreInstallReplay297.actual_before_install,real_step same yes fresh,
    before_projection,project_same same yes,models_same same yes⟩

end Yulang.GeneralRebaseRefreshInstall298
