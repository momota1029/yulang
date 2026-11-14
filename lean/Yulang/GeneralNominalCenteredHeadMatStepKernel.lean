import Yulang.GeneralNominalCenteredHeadMatStepLocal

set_option backward.isDefEq.respectTransparency false

/-! Total-materialization transitions with trusted observation updates.
Candidate matching reads cached heads. Equations, same-input merging, and
actual-position K2 use the complete journal. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepKernel
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {state before after : State roles} {effect : Effect roles} {model : Assignment}

def Committed (state : State roles) (plan : Plan roles) : Prop :=
  (∀ model, Models state model → GeneralNominalCenteredHeadMatStepPackets.Holds plan model) ∧
    ∀ child ∈ plan.packet.children, (plan.packet.site.occurrence,child) ∈ state.core.erased.current.edges

def AlternativesSafe (registry : Registry) (state : State roles) (input : Site roles) : Prop :=
  ∀ plan : Plan roles, plan.input = input →
    GeneralNominalCenteredHeadOutputs.Frame registry state.core input.occurrence plan.packet.declaration.id plan →
    GeneralNominalCenteredHeadMatStepCycles.Safe state plan

structure Installable (registry : Registry) (state : State roles) (effect : Effect roles) : Prop where
  registry_eq : effect.registry = registry
  snapshot_eq : effect.snapshot = state.core
  safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepLocal.diagnosticBoundary roles) registry state
    effect.plan.packet.site.occurrence
  cache : GeneralNominalCenteredHeadMatStepObservations.CacheSound state state.core.erased.current.context.state
  materialized : (GeneralNominalCenteredHeadMatPlans.emittedSchema effect.plan).unknown = false
  choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet
  positions : GeneralNominalCenteredHeadMatStepCycles.Safe state effect.plan
  alternatives : AlternativesSafe registry state effect.plan.input
  common : ∃ model, InstallationModels state effect model

def Equal (state : State roles) (first last : Nat) : Prop :=
  ∀ model, Models state model → CommonNominalFullCarrier.Equivalent (model first).1 (model last).1

inductive Administrative (before : State roles) : Occurrence roles → State roles → Prop
  | enqueue (focus : Occurrence roles) : GeneralNominalState.Linked before.core.erased.current.context.state focus.demand →
      (∀ site ∈ before.core.erased.current.sites, site.occurrence ≠ focus) →
      Administrative before focus (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus))
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      GeneralNominalCenteredHeadMatStepRefresh.Refresh before context → (source : Nat) →
      source ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      ¬ GeneralNominalState.Known before.core.erased.current.context.state source →
      GeneralNominalState.Known context.state source → Administrative before focus (refresh before context)
  | equate (focus : Occurrence roles) (first last : Nat) :
      first ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      last ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      Equal before first last → ¬ GeneralNominalFeedbackSteps.RawEqual before.core.erased.current first last →
      Administrative before focus (change before (GeneralNominalFeedbackSteps.equate before.core.erased.current first last))
  | reobserve (focus : Occurrence roles)
      (revision : GeneralNominalReobservationSteps.Revision before.core.erased.current) :
      GeneralNominalCenteredHeadMatStepRefresh.Reobserve before revision →
      GeneralNominalReobservationSteps.Improves revision → Administrative before focus (change before revision.result)

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop
  | administrative {focus : Occurrence roles} {after : State roles} : Administrative before focus after → At registry before focus after
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      GeneralNominalCenteredHeadMatStepRefresh.Refresh before context → (source : Nat) →
      source ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      ¬ GeneralNominalState.Known before.core.erased.current.context.state source →
      GeneralNominalState.Known context.state source → At registry before focus (refresh before context)
  | install (effect : Effect roles) : Installable registry before effect → ¬ Committed before effect.plan →
      At registry before effect.plan.packet.site.occurrence (install before effect)
  | merge (first last : Site roles) : first ∈ before.core.sites → last ∈ before.core.sites →
      SameInputs (Models before) first last →
      ¬ GeneralNominalSaturationState.Alias before.core.erased.current first.occurrence.identity last.occurrence.identity →
      At registry before first.occurrence (merge before first last)

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before.core.erased.current root focus ∧ At registry before focus after

def Stable (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.core.erased.current root focus → ∀ after, ¬ At registry state focus after

theorem administrative_models (action : Administrative before focus after) (valid : Models after model) : Models before model := by
  cases action with
  | refresh context certificate source member unknown known =>
      exact GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate |>.mp valid
  | reobserve revision certificate improved =>
      exact GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate |>.mp valid
  | enqueue linked absent =>
      refine ⟨valid.1,valid.2.1,?_,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
      · intro site member
        exact valid.2.2.1 site (List.mem_append_left _ member)
      · intro effect member
        have pair := valid.2.2.2.2.2 effect member
        exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
          (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
            (before := before.core) (after := (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus)).core)
            (fun _ h => List.mem_append_left _ h) (fun _ h => h)) pair.2⟩
  | equate first last one two equal novel =>
      refine ⟨((GeneralNominalState.extend_models ..).mp valid.1).1,
        valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
      intro effect member
      have pair := valid.2.2.2.2.2 effect member
      exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := before.core) (after := (change before (GeneralNominalFeedbackSteps.equate before.core.erased.current first last)).core)
          (fun _ h => h) (fun _ h => h)) pair.2⟩

theorem stepModels (step : Step registry root before after) (valid : Models after model) : Models before model := by
  obtain ⟨focus,_,action⟩ := step
  cases action with
  | administrative action => exact administrative_models action valid
  | refresh focus context certificate source member unknown known =>
      exact GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate |>.mp valid
  | install effect enabled novel => exact ((install_models enabled.snapshot_eq).mp valid).1
  | merge first last one two same novel => exact (merge_models.mp valid).1

theorem steps_models (path : B4Target.Steps (Step registry root) before after) :
    ∀ model, Models after model → Models before model := by
  induction path with
  | refl => exact fun _ valid => valid
  | tail _ step ih => exact fun _ valid => ih _ (stepModels step valid)

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.core.erased.current root child → Stable registry state child := by
  have stable : Stable registry state root := fun focus generated after action => halted after ⟨focus,generated,action⟩
  exact ⟨stable,fun child generated focus path => stable focus (GeneralNominalSaturationState.generated_trans generated path)⟩

theorem installable_selected (enabled : Installable registry state effect) :
    GeneralNominalCenteredHeadMatStepLocal.Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id effect.plan.packet.children) := by
  have unique := enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.unique
  have frame := enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.frame
  refine .selected enabled.safe unique ?_
  intro conflict
  obtain ⟨model,valid,branch,snapshot,_,_⟩ := enabled.common
  exact conflict.2 ⟨model,valid,⟨_,unique⟩,effect.plan,frame,enabled.snapshot_eq ▸ effect.ready,
    GeneralNominalCenteredHeadMatStepPackets.head_equations branch,enabled.snapshot_eq ▸ snapshot.2⟩

theorem installed_committed (snapshot : effect.snapshot = state.core) : Committed (install state effect) effect.plan :=
  ⟨fun _ valid => ((install_models snapshot).mp valid).2.1,fun _ member => installed_child member⟩

end Yulang.GeneralNominalCenteredHeadMatStepKernel
