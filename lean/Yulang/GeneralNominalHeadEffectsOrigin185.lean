import Yulang.GeneralNominalCenteredHeadWFBoundary
import Yulang.GeneralNominalCenteredHeadStepEnumeration

/-! Every effect in the actual head-step ledger comes from an installation
snapshot on the same trace. The core plan list is exactly its projection. -/
namespace Yulang.GeneralNominalHeadEffectsOrigin185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepTrace (configuration_trace)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem trace_plans_effects
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    state.core.plans = state.effects.map Effect.plan := by
  induction path with
  | refl => rfl
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative | refresh | merge => exact ih
    | install plan support enabled novel =>
      change plan :: before.core.plans = plan :: before.effects.map Effect.plan
      rw [ih]

theorem trace_effect_origin
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ effect ∈ state.effects, ∃ before,
      B4Target.Steps (Step registry root) (initial context root) before ∧
      effect.snapshot = before.core ∧
      effect.plan.packet.context = before.core.erased.current.context ∧
      effect.registry = registry := by
  induction path with
  | refl => intro effect member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro effect member
      rcases List.mem_cons.mp member with rfl | old
      · exact ⟨before,path,rfl,enabled.frame.context_eq,rfl⟩
      · exact ih effect old

theorem trace_effect_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.snapshot.erased.current.context.state.seed = context.state.seed ∧
    effect.snapshot.erased.current.context.state.constructors = context.state.constructors ∧
    effect.snapshot.erased.current.context.interpretation = context.interpretation := by
  obtain ⟨before,prior,snapshot,_,_⟩ := trace_effect_origin path effect member
  rw [snapshot]
  exact configuration_trace prior

theorem trace_effect_plan_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.plan.packet.context.state.seed = context.state.seed ∧
    effect.plan.packet.context.state.constructors = context.state.constructors ∧
    effect.plan.packet.context.interpretation = context.interpretation := by
  obtain ⟨before,prior,_,current,_⟩ := trace_effect_origin path effect member
  rw [current]
  exact configuration_trace prior

theorem trace_registered_plan_iff
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) :
    plan ∈ state.core.plans ↔ ∃ effect ∈ state.effects, effect.plan = plan := by
  rw [trace_plans_effects path]
  exact List.mem_map

theorem wf_plans_effects
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state) :
    state.core.plans = state.effects.map Effect.plan := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact trace_plans_effects path

theorem wf_effect_snapshot_reachable
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    ∃ before, B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root before ∧
      effect.snapshot = before.core ∧ effect.registry = registry := by
  obtain ⟨start,initialSource,path⟩ := reachable
  obtain ⟨context,labels,source,point,ground,startEq⟩ := initialSource.1
  subst start
  obtain ⟨before,prior,snapshot,_,reg⟩ := trace_effect_origin path effect member
  exact ⟨before,⟨_,initialSource,prior⟩,snapshot,reg⟩

theorem wf_effect_seed
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.snapshot.erased.current.context.state.seed = state.core.erased.current.context.state.seed := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact (trace_effect_configuration path effect member).1.trans (configuration_trace path).1.symm

end Yulang.GeneralNominalHeadEffectsOrigin185
