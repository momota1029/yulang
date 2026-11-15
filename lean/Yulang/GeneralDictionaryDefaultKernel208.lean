import Yulang.GeneralDictionaryDefaultSchema208

set_option backward.isDefEq.respectTransparency false

/-! Total-materialization transitions with trusted observation updates.
Candidate matching reads cached heads. Equations, same-input merging, and
actual-position K2 use the complete journal. -/
namespace Yulang.GeneralDictionaryDefaultKernel208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {state before after : State roles} {effect : Effect roles} {model : Assignment}

def Committed (state : State roles) (plan : Plan roles) : Prop :=
  GeneralNominalCenteredHeadMatStepKernel.Committed state plan ∧
  ∀ model, Models state model →
    GeneralDictionaryDefaultSchema208.SchemaHolds state.core plan.packet.site.occurrence plan model


def AlternativesSafe (registry : Registry) (state : State roles) (input : Site roles) : Prop :=
  ∀ plan : Plan roles, plan.input = input →
    GeneralNominalCenteredHeadOutputs.Frame registry state.core input.occurrence plan.packet.declaration.id plan →
    GeneralNominalCenteredHeadMatStepCycles.Safe state plan

abbrev Installable := @GeneralNominalCenteredHeadMatStepKernel.Installable

def Equal (state : State roles) (first last : Nat) : Prop :=
  ∀ model, Models state model → CommonNominalFullCarrier.Equivalent (model first).1 (model last).1

abbrev Administrative := @GeneralNominalCenteredHeadMatStepKernel.Administrative

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

theorem installed_committed (snapshot : effect.snapshot = state.core) : Committed (install state effect) effect.plan := by
  refine ⟨GeneralNominalCenteredHeadMatStepKernel.installed_committed snapshot,?_⟩
  intro model valid
  have parts := (install_models snapshot).mp valid
  exact GeneralDictionaryDefaultSchema208.schema_holds_iff.mpr ⟨parts.2.1.2.2,parts.2.2.2.1⟩

theorem committed_packet (given : Committed state plan) :
    GeneralNominalCenteredHeadMatStepKernel.Committed state plan := given.1

theorem committed_class (given : Committed state plan) (valid : Models state model) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects state.core plan.packet.site.occurrence plan model :=
  (GeneralDictionaryDefaultSchema208.schema_holds_iff.mp (given.2 model valid)).2

/-- Old install steps remain valid; additional installs can record missing defaults. -/
theorem old_at (action : GeneralNominalCenteredHeadMatStepKernel.At registry state focus after) :
    At registry state focus after := by
  cases action with
  | administrative action => exact .administrative action
  | refresh focus context cert source member unknown known => exact .refresh focus context cert source member unknown known
  | install effect enabled novel => exact .install effect enabled (fun committed => novel committed.1)
  | merge first last one two same novel => exact .merge first last one two same novel

theorem stable_old (stable : Stable registry state root) :
    GeneralNominalCenteredHeadMatStepKernel.Stable registry state root :=
  fun focus generated after action => stable focus generated after (old_at action)

end Yulang.GeneralDictionaryDefaultKernel208
