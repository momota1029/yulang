import Yulang.GeneralNominalPointRevision240
set_option backward.isDefEq.respectTransparency false
/-! I45 successor. Only Reobserve receives the exact old-point descriptor guard.
Versioned allocation, trusted caches and all other operational guards stay unchanged.
Erasure to234 is proved; there is no unrestricted old-step embedding. -/
namespace Yulang.GeneralNominalPointKernel240
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
abbrev Committed := @GeneralNominalVersionedInstallStep232.Committed

abbrev AlternativesSafe := @GeneralNominalVersionedMixedKernel234.AlternativesSafe
abbrev Installable := @GeneralNominalVersionedMixedKernel234.Installable
abbrev Equal := @GeneralNominalVersionedMixedKernel234.Equal

inductive Administrative (before : State roles) : Occurrence roles → State roles → Prop
  | enqueue (focus : Occurrence roles) : GeneralNominalState.Linked before.core.erased.current.context.state focus.demand →
      (∀ site ∈ before.core.erased.current.sites, site.occurrence ≠ focus) →
      Administrative before focus (GeneralNominalVersionedAdministrative232.enqueue before focus)
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      GeneralNominalVersionedMixedObservations233.Refresh before context → (source : Nat) →
      source ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      ¬ GeneralNominalState.Known before.core.erased.current.context.state source →
      GeneralNominalState.Known context.state source →
      Administrative before focus (GeneralNominalVersionedRefresh232.refresh before context)
  | equate (focus : Occurrence roles) (first last : Nat) :
      first ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      last ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      Equal before first last → ¬ GeneralNominalFeedbackSteps.RawEqual before.core.erased.current first last →
      Administrative before focus (GeneralNominalVersionedAdministrative232.equate before first last)
  | reobserve (focus : Occurrence roles)
      (revision : GeneralNominalReobservationSteps.Revision before.core.erased.current) :
      GeneralNominalVersionedMixedObservations233.Reobserve before revision →
      GeneralNominalReobservationSteps.Improves revision →
      GeneralNominalPointRevision240.Preserves revision →
      Administrative before focus (GeneralNominalVersionedRefresh232.reobserve before revision)

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop
  | administrative : Administrative before focus after → At registry before focus after
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      GeneralNominalVersionedMixedObservations233.Refresh before context → (source : Nat) →
      source ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      ¬ GeneralNominalState.Known before.core.erased.current.context.state source →
      GeneralNominalState.Known context.state source →
      At registry before focus (GeneralNominalVersionedRefresh232.refresh before context)
  | install (effect : Effect roles) : Installable registry before effect → ¬ Committed before effect.plan →
      At registry before effect.plan.packet.site.occurrence (install before effect)
  | merge (first last : Site roles) : first ∈ before.core.sites → last ∈ before.core.sites →
      SameInputs (Models before) first last →
      ¬ GeneralNominalSaturationState.Alias before.core.erased.current first.occurrence.identity last.occurrence.identity →
      At registry before first.occurrence (GeneralNominalVersionedAdministrative232.merge before first last)

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before.core.erased.current root focus ∧ At registry before focus after

def Stable (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.core.erased.current root focus → ∀ after, ¬ At registry state focus after

theorem administrative_models (action : Administrative before focus after) (valid : Models after model) :
    Models before model := by
  cases action with
  | enqueue => exact GeneralNominalVersionedAdministrative232.enqueue_models valid
  | equate => exact GeneralNominalVersionedAdministrative232.equate_models valid
  | refresh context certificate source member unknown known =>
    exact (GeneralNominalVersionedMixedObservations233.refresh_models certificate).mp valid
  | reobserve revision certificate improved preserved =>
    exact (GeneralNominalVersionedMixedObservations233.reobserve_models certificate).mp valid

theorem step_models (step : Step registry root before after) (valid : Models after model) :
    Models before model := by
  obtain ⟨focus,_,action⟩ := step
  cases action with
  | administrative action => exact administrative_models action valid
  | refresh focus context certificate source member unknown known =>
    exact (GeneralNominalVersionedMixedObservations233.refresh_models certificate).mp valid
  | install effect enabled _ => exact GeneralNominalVersionedInstall232.step_models enabled.snapshot_eq valid
  | merge => exact GeneralNominalVersionedAdministrative232.merge_restrict valid

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.core.erased.current root child → Stable registry state child := by
  have stable : Stable registry state root := fun focus generated next action => halted next ⟨focus,generated,action⟩
  exact ⟨stable,fun child generated focus path => stable focus (GeneralNominalSaturationState.generated_trans generated path)⟩

theorem steps_models (path : B4Target.Steps (Step registry root) before after) (valid : Models after model) :
    Models before model := by
  induction path with
  | refl => exact valid
  | tail path step ih => exact ih (step_models step valid)


end Yulang.GeneralNominalPointKernel240
