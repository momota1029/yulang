import Yulang.GeneralNominalVersionedMixedRoles235
set_option backward.isDefEq.respectTransparency false
/-! Source coverage yields actual current Ready and emitted-schema completeness.
These are derived guards, not additional assumptions on selected programs. -/
namespace Yulang.GeneralNominalVersionedMixedReady235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem coverage
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    GeneralNominalCenteredHeadWFSource.Coverage (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core.erased.current.context.interpretation := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,covered,sameLegacy⟩,same⟩,path⟩ := path
  subst first
  subst legacy
  rw [(GeneralNominalVersionedMixedGrowth234.steps path).interpretation]
  exact GeneralNominalCenteredHeadAllocEncoding.coverage covered

theorem ready (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core focus key plan) : GeneralNominalCenteredHeadMatEffects.Ready state.core focus plan := by
  apply GeneralNominalCenteredHeadMatEffects.ready_of_wf
  · rw [frame.registry_eq,frame.context_eq]; exact coverage path
  · rw [frame.registry_eq]; exact frame.visible
  · rw [frame.registry_eq]; exact checked.1
  · exact GeneralNominalVersionedMixedRoles235.requests_declared checked path frame

theorem emitted_covered {plan : Plan roles}
    (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered
      plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration) :
    GeneralNominalCenteredHeadMatSchemas.RequestsCovered plan.packet.registry.constructors
      plan.packet.context.interpretation (GeneralNominalVersionedPlans231.emittedRequests plan.packet) := by
  intro request member
  rcases List.mem_append.mp member with rootRequest | emitted
  · obtain ⟨output,_,within⟩ := List.mem_flatMap.mp rootRequest
    obtain ⟨equation,found,rfl⟩ := List.mem_map.mp within
    exact covered.2.2 equation (List.mem_of_find?_eq_some (Option.mem_toList.mp found))
  · obtain ⟨emission,present,within⟩ := List.mem_flatMap.mp emitted
    have perm := GeneralCanonicalChildOrder.canonicalEmit_perm plan.packet.site.occurrence.identity
      plan.packet.declaration plan.packet.checked (GeneralNominalVersionedFrame231.capture plan.packet)
      ((GeneralNominalVersionedFrame231.frame plan.packet).allocation plan.packet.declaration.id)
    obtain ⟨clause,_,equal⟩ := List.mem_map.mp (perm.mem_iff.mpr present)
    subst emission
    exact GeneralNominalCenteredHeadMatSchemas.emitted_covered (covered.2.1 clause.val clause.property).1
      (covered.2.1 clause.val clause.property).2 _ request within

theorem materialized
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core focus key plan) : (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false := by
  apply GeneralNominalCenteredHeadMatSchemas.generated_complete
  apply emitted_covered
  rw [frame.registry_eq,frame.context_eq]
  exact (coverage path).1 _ frame.visible

end Yulang.GeneralNominalVersionedMixedReady235
