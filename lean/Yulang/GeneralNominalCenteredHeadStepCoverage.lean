import Yulang.GeneralNominalCenteredHeadStepKernel

set_option backward.isDefEq.respectTransparency false

/-! Installation records every request in the chosen class. Historical
coverage persists, and merges impose the equations of the enlarged live class. -/
namespace Yulang.GeneralNominalCenteredHeadStepCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadOutputs
variable {roles : Roles.RoleDecls} {state before after : State roles} {plan : Plan roles}

def OutputEffectCoverage (registry : Registry) (before after : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ model, Models after model → ChosenClassEffects registry before.core root key model

theorem installed_coverage (enabled : Installable registry state plan support) :
    OutputEffectCoverage registry state (install state plan support enabled)
      plan.packet.site.occurrence plan.packet.declaration.id := by
  intro model valid
  exact recorded_effects (effect := record enabled) (List.mem_cons_self ..) valid

theorem coverage_steps (covered : OutputEffectCoverage registry snapshot before root key)
    (path : B4Target.Steps (Step actionRegistry saturationRoot) before after) :
    OutputEffectCoverage registry snapshot after root key :=
  fun model valid => covered model (steps_models path model valid)

theorem requests_step (step : Step registry saturationRoot before after) :
    requests before.core root ⊆ requests after.core root := requests_mono (at_extends step.choose_spec.2).journal

theorem effects_step (step : Step registry root before after) : before.effects ⊆ after.effects := by
  obtain ⟨focus,_,action⟩ := step
  cases action with
  | administrative | refresh | merge => exact fun _ member => member
  | install => exact fun _ member => List.mem_cons_of_mem _ member

theorem effects_steps (path : B4Target.Steps (Step registry root) before after) : before.effects ⊆ after.effects := by
  induction path with
  | refl => exact fun _ member => member
  | tail path step ih => exact fun _ member => effects_step step (ih member)

theorem installed_live_after_steps (enabled : Installable registry state plan support)
    (path : B4Target.Steps (Step registry root) (install state plan support enabled) after)
    (valid : Models after model) : OutputEquations after.core plan.packet.site.occurrence plan model :=
  (valid.2 (record enabled) (effects_steps path (List.mem_cons_self ..))).2

theorem installed_live_coverage (enabled : Installable registry state plan support)
    (valid : Models (install state plan support enabled) model) :
    OutputEquations (install state plan support enabled).core plan.packet.site.occurrence plan model :=
  (valid.2 (record enabled) (List.mem_cons_self ..)).2

theorem merge_extends (state : State roles) (first last : Site roles) (support : List (Occurrence roles)) :
    GeneralNominalSaturationSteps.Extends state.core.erased.current (merge state first last support).core.erased.current :=
  ⟨fun _ valid => ((GeneralNominalSaturationState.merge_models ..).mp valid).1,
    fun _ member => member,fun _ member => member,fun _ member => List.mem_cons_of_mem _ member,
    fun _ known => known⟩

theorem merge_models (state : State roles) (first last : Site roles) (support : List (Occurrence roles)) (model) :
    Models (merge state first last support) model ↔
      Models state model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) ∧
      ∀ effect ∈ state.effects, effect.Live (merge state first last support).core model := by
  constructor
  · intro valid
    have raw := (GeneralNominalSaturationState.merge_models ..).mp valid.1.1
    refine ⟨⟨⟨raw.1,valid.1.2⟩,?_⟩,raw.2,fun effect member => (valid.2 effect member).2⟩
    intro effect member
    exact ⟨(valid.2 effect member).1,
      live_restrict effect (merge_extends state first last support) (valid.2 effect member).2⟩
  · rintro ⟨valid,equalities,live⟩
    exact ⟨⟨(GeneralNominalSaturationState.merge_models ..).mpr ⟨valid.1.1,equalities⟩,valid.1.2⟩,
      fun effect member => ⟨(valid.2 effect member).1,live effect member⟩⟩

theorem coverage_merge (covered : OutputEffectCoverage registry snapshot state root key)
    (first last : Site roles) (support : List (Occurrence roles)) :
    OutputEffectCoverage registry snapshot (merge state first last support) root key :=
  fun model valid => covered model ((merge_models state first last support model).mp valid).1

theorem live_merged_class (recorded : effect ∈ state.effects)
    (valid : Models (merge state first last support) model) :
    OutputEquations (merge state first last support).core effect.plan.packet.site.occurrence effect.plan model :=
  (valid.2 effect recorded).2

theorem live_merged_equal_outputs (recorded : effect ∈ state.effects)
    (valid : Models (merge state first last support) model) :
    EqualOutputs (merge state first last support).core effect.plan.packet.site.occurrence model :=
  (live_merged_class recorded valid).2

theorem merged_one_sided_request (first last : Site roles)
    (empty : first.occurrence.demand.outputs = [])
    (member : last.observed ∈ state.core.erased.current.sites)
    (within : output ∈ last.occurrence.demand.outputs) (support) :
    output ∈ requests (merge state first last support).core first.occurrence :=
  one_sided_request state.core first last empty member within support

end Yulang.GeneralNominalCenteredHeadStepCoverage
