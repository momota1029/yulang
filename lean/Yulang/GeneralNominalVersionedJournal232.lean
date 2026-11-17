import Yulang.GeneralNominalVersionedEvidence231
import Yulang.GeneralNominalVersionedInstallation231
set_option backward.isDefEq.respectTransparency false

/-! A mixed historical journal: legacy packets keep their legacy interpretation;
newly installed packets and effects have the versioned interpretation. -/
namespace Yulang.GeneralNominalVersionedJournal232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
namespace Legacy
abbrev State := GeneralNominalCenteredHeadMatStepJournal.State
abbrev Models := @GeneralNominalCenteredHeadMatStepJournal.Models
end Legacy

structure Effect (roles : Roles.RoleDecls) where
  registry : Registry
  snapshot : GeneralNominalCenteredSteps.State roles
  plan : Plan roles
  frame : GeneralNominalVersionedEvidence231.Frame registry snapshot
    plan.packet.site.occurrence plan.packet.declaration.id plan
  unique : GeneralNominalVersionedCandidates231.Unique registry snapshot.erased.current.context
    plan.packet.site.occurrence plan.packet.declaration.id (GeneralNominalVersionedFrame231.children plan.packet)
  ready : GeneralNominalCenteredHeadMatEffects.Ready snapshot plan.packet.site.occurrence plan

def Effect.Holds (effect : Effect roles) (model : Assignment) : Prop :=
  GeneralNominalVersionedPlans231.HeadModels effect.plan.packet model ∧
    GeneralNominalVersionedEffects231.ClassEffects effect.snapshot effect.plan.packet.site.occurrence effect.plan model

def Effect.Live (effect : Effect roles) (core : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) : Prop :=
  GeneralNominalVersionedEffects231.ClassEffects core effect.plan.packet.site.occurrence effect.plan model

structure State (roles : Roles.RoleDecls) where
  legacy : Legacy.State roles
  plans : List (Plan roles) := []
  effects : List (Effect roles) := []

abbrev State.core (state : State roles) := state.legacy.core

def Models (state : State roles) (model : Assignment) : Prop :=
  Legacy.Models state.legacy model ∧
    (∀ plan ∈ state.plans, GeneralNominalVersionedPlans231.Holds plan model) ∧
    ∀ effect ∈ state.effects, effect.Holds model ∧ effect.Live state.core model

def lift (legacy : Legacy.State roles) : State roles := ⟨legacy,[],[]⟩

theorem lift_models (legacy : Legacy.State roles) (model : Assignment) :
    Models (lift legacy) model ↔ Legacy.Models legacy model := by
  constructor
  · exact And.left
  · intro valid
    exact ⟨valid,(by intro _ member; cases member),(by intro _ member; cases member)⟩

def initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : State roles :=
  lift (GeneralNominalCenteredHeadMatStepJournal.initial context root)

theorem initial_models (context : GeneralNominalCandidates.Context) (root : Occurrence roles) (model : Assignment) :
    Models (initial context root) model ↔ GeneralNominalState.Models context.state model ∧
      (rootSite context.state.seed root).Holds model := by
  rw [initial,lift_models]
  exact GeneralNominalCenteredHeadMatStepJournal.initial_models context root model

theorem legacy_models (valid : Models state model) : Legacy.Models state.legacy model := valid.1

theorem plan_models (valid : Models state model) (present : plan ∈ state.plans) :
    GeneralNominalVersionedPlans231.Holds plan model := valid.2.1 plan present

theorem effect_models (valid : Models state model) (present : effect ∈ state.effects) :
    effect.Holds model ∧ effect.Live state.core model := valid.2.2 effect present

/-- Live class equations restrict along retained output requests. -/
theorem live_restrict {effect : Effect roles} {before after : GeneralNominalCenteredSteps.State roles}
    (requests : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests before effect.plan.packet.site.occurrence,
      output ∈ GeneralNominalCenteredHeadOutputs.requests after effect.plan.packet.site.occurrence)
    (valid : effect.Live after model) : effect.Live before model :=
  (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
    (GeneralNominalCenteredHeadMatEffects.restrict requests
      ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp valid))

end Yulang.GeneralNominalVersionedJournal232
