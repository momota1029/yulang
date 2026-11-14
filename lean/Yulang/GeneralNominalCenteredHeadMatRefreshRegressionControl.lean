import Yulang.GeneralNominalCenteredHeadMatRefreshRegressionTrace

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatRefreshRegressionControl
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSourceUnsettledRefreshWitness
open GeneralNominalCenteredSourceUnsettledRefreshDecision (controlContext controlSource)
open GeneralNominalCenteredHeadMatRefreshRegressionSource
open GeneralNominalCenteredHeadMatRefreshRegressionTrace
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepObservations
open GeneralNominalCenteredHeadMatStepRefresh
open GeneralNominalCenteredHeadMatStepKernel (Step)
open CommonNominalFullCarrier

def kept : State roles := refresh installed controlContext

theorem control_cache : CacheSound installed controlSource := by
  intro observation recorded
  refine ⟨[],.source,?_⟩
  intro model valid
  cases recorded with
  | scalar slot scalar head =>
      exact GeneralNominalCenteredSourceUnsettledRefreshDecision.control_observations_source_supported
        (.scalar slot scalar head) model valid.1
  | structural slot kind children head =>
      exact GeneralNominalCenteredSourceUnsettledRefreshDecision.control_observations_source_supported
        (.structural slot kind children head) model valid.1
  | nominal slot descriptor head =>
      exact GeneralNominalCenteredSourceUnsettledRefreshDecision.control_observations_source_supported
        (.nominal slot descriptor head) model valid.1

noncomputable def certificate : Refresh installed controlContext where
  refines := GeneralNominalCenteredSourceUnsettledRefreshDecision.controlCertificate.refines
  interpretation := rfl
  support := refreshed_support
  constraints := fun model valid =>
    let sourceModels := refreshed_exact model (installed_legacy model valid)
    ⟨sourceModels.1,sourceModels.2.2⟩
  cache := control_cache

theorem control_step : Step registry root installed kept :=
  ⟨root,.root,.refresh root controlContext certificate 3
    (GeneralNominalAllocationSupport.slot_source installed.core.erased.current.context.state (3 : Fin 4)) progress_unknown
    (GeneralNominalCenteredSourceUnsettledRefreshDecision.control_known 3 progress_known)⟩

theorem control_trace : B4Target.Steps (Step registry root) start kept :=
  .tail (.tail .refl GeneralNominalCenteredHeadMatRefreshRegressionTrace.stepP) control_step

theorem kept_model : Models kept witness := (refresh_models certificate).mpr installed_model

theorem installed_sites : installed.core.sites = [planP.input,emittedChild] := by
  change [planP.input] ++ planP.emitted = _
  rw [emitted_exact]
  rfl

theorem equal_registered_sites (one : first ∈ installed.core.sites) (two : last ∈ installed.core.sites)
    (equal : first.occurrence.identity = last.occurrence.identity) : first = last := by
  rw [installed_sites] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · rfl
  · exact False.elim (child_identity_not_root equal.symm)
  · exact False.elim (child_identity_not_root equal)
  · rfl

theorem registered_single_output (member : site ∈ installed.core.sites) :
    ∃ output, site.occurrence.demand.outputs = [output] := by
  rw [installed_sites] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨⟨0,2⟩,rfl⟩
  · cases List.mem_singleton.mp member
    exact ⟨⟨0,outputP⟩,rfl⟩

theorem counter_cut : Cut installed sourceCounter := by
  apply cut_of_recorded counter_source
  · intro site member
    cases List.mem_singleton.mp member
    exact point_root_holds source.seed root (fun _ => rfl) sourceCounter
  · intro plan member
    cases List.mem_singleton.mp member
    exact input_models sourceCounter counter_source
  · intro effect member recorded settled
    exact False.elim (installed_unsettled effect.plan.packet settled)
  · intro first one last two alias atoms
    have same := equal_registered_sites one two (aliases_eq alias)
    subst last
    obtain ⟨output,outputs⟩ := registered_single_output one
    apply (GeneralNominalDemandMerging.output_atoms_exact _ _ sourceCounter).mpr
    intro a present b found _
    change a ∈ first.occurrence.demand.outputs at present
    change b ∈ first.occurrence.demand.outputs at found
    rw [outputs] at present found
    cases List.mem_singleton.mp present
    cases List.mem_singleton.mp found
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem no_redirected_refresh : ¬ Nonempty (Refresh installed refreshedContext) :=
  refresh_excluded counter_cut (.structural 1 0 (fun _ => 3) rfl) redirected_head_false

theorem no_redirected_reobserve
    (revision : GeneralNominalReobservationSteps.Revision installed.core.erased.current)
    (recorded : GeneralCanonicalObservations.Recorded revision.snapshot
      (.normalized refreshedBase 1 (.pair (.var 3) (.var 3)))) : ¬ Reobserve installed revision :=
  reobserve_excluded counter_cut recorded redirected_head_false

theorem kept_cut : Cut kept sourceCounter := by
  intro facts trusted
  have reverse : GeneralNominalCenteredHeadMatStepTrustedGrowth.Growth kept installed :=
    ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
      fun _ h => h,fun _ h => h,fun _ h => h⟩
  have before := GeneralNominalCenteredHeadMatStepTrustedGrowth.trusted reverse trusted
  exact counter_cut facts before

theorem no_redirected_refresh_kept : ¬ Nonempty (Refresh kept refreshedContext) :=
  refresh_excluded kept_cut (.structural 1 0 (fun _ => 3) rfl) redirected_head_false

end Yulang.GeneralNominalCenteredHeadMatRefreshRegressionControl
