import Yulang.GeneralNominalVersionedMixedTrace235
import Yulang.GeneralNominalCenteredHeadMatStepRoles
set_option backward.isDefEq.respectTransparency false
/-! Invocation colors and declared output requests survive actual versioned
emission. Aggregate versions do not alter child identity or child role. -/
namespace Yulang.GeneralNominalVersionedMixedRoles235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalCenteredHeadMatStepRoles (Origin Invariant origin_above)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {before after state : State roles}

theorem emitted_origin (valid : Invariant registry seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (member : site ∈ GeneralNominalVersionedChildren232.emitted plan) :
    Origin registry seed root site.occurrence := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  refine Or.inr ⟨plan.packet.site.occurrence.identity,plan.packet.declaration,frame.visible,
    clause.val,visible,origin_above (valid.raw _ frame.raw_recorded),?_,rfl⟩
  change GeneralNominalIdentities.source plan.packet.context.state.seed _ = _
  rw [frame.context_eq,valid.seed_eq]
  rfl

theorem install (valid : Invariant registry seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core
      effect.plan.packet.site.occurrence effect.plan.packet.declaration.id effect.plan) :
    Invariant registry seed root (GeneralNominalVersionedInstall232.install state effect).core := by
  refine ⟨?_,?_,valid.aliases,?_⟩
  · intro site member
    rcases List.mem_append.mp member with old | added
    · exact valid.raw site old
    · obtain ⟨center,present,rfl⟩ := List.mem_map.mp added
      exact emitted_origin valid frame present
  · intro site member
    exact (List.mem_append.mp member).elim (valid.centers site) (emitted_origin valid frame)
  · change effect.plan.packet.context.state.seed = seed
    rw [frame.context_eq,valid.seed_eq]

theorem step (checked : Checked registry)
    (recorded : GeneralNominalVersionedMixedTrace235.Registered before root)
    (valid : Invariant registry seed root before.core)
    (action : Step registry root before after) : Invariant registry seed root after.core := by
  obtain ⟨focus,generated,action⟩ := action
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered recorded generated
      exact False.elim (absent site present same)
    | equate | reobserve => exact ⟨valid.raw,valid.centers,valid.aliases,valid.seed_eq⟩
    | refresh _ certificate _ _ _ _ =>
      exact ⟨valid.raw,valid.centers,valid.aliases,certificate.refines.seed.trans valid.seed_eq⟩
  | refresh _ _ certificate _ _ _ _ =>
    exact ⟨valid.raw,valid.centers,valid.aliases,certificate.refines.seed.trans valid.seed_eq⟩
  | merge first last one two same novel =>
    exact GeneralNominalCenteredHeadMatStepRoles.merge checked valid one two same.1
  | install effect enabled novel =>
    exact install valid (enabled.registry_eq ▸ enabled.snapshot_eq ▸ effect.frame)

theorem trace (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (GeneralNominalVersionedJournal232.initial context root) state) :
    Invariant registry context.state.seed root state.core := by
  induction path with
  | refl => exact GeneralNominalCenteredHeadMatStepRoles.initial context root
  | tail path action ih =>
    exact step checked (GeneralNominalVersionedMixedTrace235.steps
      (GeneralNominalVersionedMixedTrace235.initial context) path).1 ih action

theorem reachable (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    Invariant (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core.erased.source.state.seed root state.core := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := path
  subst first
  subst legacy
  have result := trace (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 path
  have origin := GeneralNominalVersionedMixedGrowth234.steps_source path
  rw [origin]
  exact result

theorem requests_declared (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core focus key plan) :
    GeneralNominalCenteredHeadDefaultSchemas.RequestsDeclared state.core focus plan := by
  have valid := reachable checked path
  have compiled := (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
  intro output member
  obtain ⟨site,present,alias,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  have focusOrigin := frame.occurrence_eq ▸ valid.raw _ frame.raw_recorded
  have colors := GeneralNominalCenteredHeadMatStepRoles.alias_color valid alias
  rw [GeneralNominalCenteredHeadMatStepRoles.color_of_origin compiled focusOrigin,
    GeneralNominalCenteredHeadMatStepRoles.color_of_origin compiled (valid.raw _ present)] at colors
  have declared := site.occurrence.demand.declared output within
  simpa only [frame.role_eq,colors] using declared

end Yulang.GeneralNominalVersionedMixedRoles235
