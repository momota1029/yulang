import Yulang.GeneralNominalVersionedKernelCache232
import Yulang.GeneralNominalVersionedSourceBoundary232
set_option backward.isDefEq.respectTransparency false
/-! Structural monotonicity of the actual mixed-journal kernel. Historical
versioned plans/effects and generated graph data are retained; source context
and current allocation seed do not change. These are not claims of termination,
new trusted-fact completeness, or semantic equality between distinct versions. -/
namespace Yulang.GeneralNominalVersionedGrowth233
open GeneralNominalVersionedJournal232 GeneralNominalVersionedKernel232
open GeneralNominalCenteredHeadMatStepTrustedGrowth (Growth)
variable {roles : Roles.RoleDecls} {before middle after : State roles}

structure Monotone (before after : State roles) : Prop where
  legacy : Growth before.legacy after.legacy
  plans : before.plans ⊆ after.plans
  effects : before.effects ⊆ after.effects
  edges : before.core.erased.current.edges ⊆ after.core.erased.current.edges
  seed : after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed
  constructors : after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors
  interpretation : after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation

theorem refl (state : State roles) : Monotone state state :=
  ⟨⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
    fun _ h => h,fun _ h => h⟩,fun _ h => h,fun _ h => h,fun _ h => h,rfl,rfl,rfl⟩

theorem trans (first : Monotone before middle) (last : Monotone middle after) : Monotone before after :=
  ⟨⟨last.legacy.source.trans first.legacy.source,last.legacy.sourceSites.trans first.legacy.sourceSites,
    fun _ h => last.legacy.sites (first.legacy.sites h),fun _ h => last.legacy.plans (first.legacy.plans h),
    fun _ h => last.legacy.effects (first.legacy.effects h),fun _ h => last.legacy.rawSites (first.legacy.rawSites h),
    fun _ h => last.legacy.packets (first.legacy.packets h),fun _ h => last.legacy.aliases (first.legacy.aliases h),
    fun _ h => last.legacy.ordinary (first.legacy.ordinary h)⟩,
    fun _ h => last.plans (first.plans h),fun _ h => last.effects (first.effects h),
    fun _ h => last.edges (first.edges h),last.seed.trans first.seed,
    last.constructors.trans first.constructors,last.interpretation.trans first.interpretation⟩

theorem administrative (action : Administrative before focus after) : Monotone before after := by
  refine ⟨GeneralNominalVersionedKernelCache232.administrative_growth action,?_,?_,?_,?_,?_,?_⟩
  · cases action <;> exact fun _ h => h
  · cases action <;> exact fun _ h => h
  · cases action <;> exact fun _ h => h
  · cases action with
    | refresh _ certificate _ _ _ _ => exact certificate.refines.seed
    | enqueue => rfl
    | equate => rfl
    | reobserve => rfl
  · cases action with
    | refresh _ certificate _ _ _ _ => exact certificate.refines.constructors
    | enqueue => rfl
    | equate => rfl
    | reobserve => rfl
  · cases action with
    | refresh _ certificate _ _ _ _ => exact certificate.interpretation
    | enqueue => rfl
    | equate => rfl
    | reobserve => rfl

theorem at_growth (action : At registry before focus after) : Monotone before after := by
  cases action with
  | administrative action => exact administrative action
  | refresh focus context certificate source member unknown known =>
    exact administrative (.refresh focus context certificate source member unknown known)
  | merge first last one two same novel =>
    exact ⟨GeneralNominalVersionedKernelCache232.at_growth
      (registry := registry) (.merge first last one two same novel),
      fun _ h => h,fun _ h => h,fun _ h => h,rfl,rfl,rfl⟩
  | install effect enabled novel =>
    refine ⟨GeneralNominalVersionedKernelCache232.at_growth (.install effect enabled novel),
      fun _ h => List.mem_cons_of_mem _ h,fun _ h => List.mem_cons_of_mem _ h,
      fun _ h => List.mem_append_left _ h,?_,?_,?_⟩
    all_goals
      have same := effect.frame.context_eq.trans
        (congrArg (fun core => core.erased.current.context) enabled.snapshot_eq)
    · change effect.plan.packet.context.state.seed = before.core.erased.current.context.state.seed
      rw [same]
    · change effect.plan.packet.context.state.constructors = before.core.erased.current.context.state.constructors
      rw [same]
    · change effect.plan.packet.context.interpretation = before.core.erased.current.context.interpretation
      rw [same]

theorem step (action : Step registry root before after) : Monotone before after := at_growth action.choose_spec.2

theorem steps (path : B4Target.Steps (Step registry root) before after) : Monotone before after := by
  induction path with
  | refl => exact refl _
  | tail _ action ih => exact trans ih (step action)

theorem step_source (action : Step registry root before after) : after.core.erased.source = before.core.erased.source :=
  (step action).legacy.source

theorem steps_source (path : B4Target.Steps (Step registry root) before after) :
    after.core.erased.source = before.core.erased.source := (steps path).legacy.source

theorem steps_source_seed (path : B4Target.Steps (Step registry root) before after) :
    after.core.erased.source.state.seed = before.core.erased.source.state.seed :=
  congrArg (fun context => context.state.seed) (steps_source path)

theorem steps_plans (path : B4Target.Steps (Step registry root) before after) : before.plans ⊆ after.plans :=
  (steps path).plans

theorem steps_effects (path : B4Target.Steps (Step registry root) before after) : before.effects ⊆ after.effects :=
  (steps path).effects

theorem steps_sites (path : B4Target.Steps (Step registry root) before after) : before.core.sites ⊆ after.core.sites :=
  (steps path).legacy.sites

theorem steps_edges (path : B4Target.Steps (Step registry root) before after) :
    before.core.erased.current.edges ⊆ after.core.erased.current.edges := (steps path).edges


theorem generated (growth : Monotone before after)
    (given : GeneralNominalSaturationState.Generated before.core.erased.current root focus) :
    GeneralNominalSaturationState.Generated after.core.erased.current root focus := by
  induction given with
  | root => exact .root
  | child _ member ih => exact .child ih (growth.edges member)
  | alias _ one two same ih =>
    exact .alias ih (growth.legacy.rawSites one) (growth.legacy.rawSites two)
      (GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases growth.legacy same)

theorem steps_generated (path : B4Target.Steps (Step registry root) before after)
    (given : GeneralNominalSaturationState.Generated before.core.erased.current parent focus) :
    GeneralNominalSaturationState.Generated after.core.erased.current parent focus := generated (steps path) given

theorem requests (growth : Monotone before after) :
    GeneralNominalCenteredHeadOutputs.requests before.core root ⊆
      GeneralNominalCenteredHeadOutputs.requests after.core root :=
  GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
    (fun _ h => growth.legacy.rawSites h) (fun _ h => growth.legacy.aliases h)

theorem steps_requests (path : B4Target.Steps (Step registry root) before after) :
    GeneralNominalCenteredHeadOutputs.requests before.core focus ⊆
      GeneralNominalCenteredHeadOutputs.requests after.core focus := requests (steps path)

theorem reachable_origin
    (reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) registry root after) :
    ∃ initial, (GeneralNominalVersionedSourceBoundary232.boundary roles).Initial registry root initial ∧
      Monotone initial after ∧ after.core.erased.source = initial.core.erased.source ∧
      after.core.erased.current.context.state.seed = initial.core.erased.current.context.state.seed := by
  obtain ⟨initial,start,path⟩ := reachable
  have grows := steps path
  exact ⟨initial,start,grows,grows.legacy.source,grows.seed⟩

theorem reachable_source_seed
    (reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) registry root after) :
    after.core.erased.current.context.state.seed = after.core.erased.source.state.seed := by
  obtain ⟨initial,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := reachable
  subst initial
  subst legacy
  have grows := steps path
  rw [grows.seed,grows.legacy.source]
  rfl

end Yulang.GeneralNominalVersionedGrowth233
