import Yulang.GeneralNominalVersionedMixedAncestry237
/-! A real finite pool for every enabled installation's invocation and its
nonaggregate allocations. Aggregate observation versions are explicitly NOT
covered by this pool. This theorem is not full installation termination. -/
namespace Yulang.GeneralNominalVersionedInvocationPool237
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedMixedAncestry237
open GeneralNominalInvocationAncestry (frontier allocationPool)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}

theorem nonaggregate_declaration_key
    (member : key ∈ GeneralNominalVersionedAllocation231.declarationKeys invocation declaration bindings)
    (lower : key.2.2.1 ≠ 0) (upper : key.2.2.1 ≠ 1) :
    key ∈ GeneralNominalAllocation.declarationKeys invocation declaration := by
  unfold GeneralNominalVersionedAllocation231.declarationKeys at member
  unfold GeneralNominalAllocation.declarationKeys
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with aggregate | output
    · obtain ⟨name,_,member⟩ := List.mem_flatMap.mp aggregate
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact False.elim (lower rfl)
      · exact False.elim (upper rfl)
    · exact List.mem_append_left _ (List.mem_append_right _ output)
  · exact List.mem_append_right _ member

theorem nonaggregate_key
    (member : key ∈ GeneralNominalVersionedAllocation231.keys registry invocation bindings)
    (lower : key.2.2.1 ≠ 0) (upper : key.2.2.1 ≠ 1) :
    key ∈ GeneralNominalAllocation.keys registry invocation := by
  obtain ⟨declaration,visible,member⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨declaration,visible,nonaggregate_declaration_key member lower upper⟩

theorem enabled_parent
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (enabled : Installable registry state effect) :
    effect.plan.packet.site.occurrence.identity ∈ frontier registry context.state.seed root.identity (mass rootLabels) := by
  obtain ⟨model,valid,_⟩ := enabled.common
  obtain ⟨depth,labels,ancestry,_,bounded⟩ := sites_bounded source point ground coverage path
    model valid effect.plan.input (frame enabled).center_recorded
  apply GeneralNominalInvocationAncestry.bounded_enumerated (depth := depth)
  · simpa only [effect.plan.input_exact] using ancestry
  · omega

theorem enabled_nonaggregate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (enabled : Installable registry state effect)
    (member : key ∈ GeneralNominalVersionedAllocation231.keys effect.plan.packet.registry
      effect.plan.packet.site.occurrence.identity effect.plan.packet.bindings)
    (lower : key.2.2.1 ≠ 0) (upper : key.2.2.1 ≠ 1) :
    GeneralNominalIdentities.source effect.plan.packet.context.state.seed key ∈
      allocationPool registry context.state.seed
        (frontier registry context.state.seed root.identity (mass rootLabels)) := by
  have present := nonaggregate_key member lower upper
  have framed := frame enabled
  rw [framed.registry_eq] at present
  have seed : effect.plan.packet.context.state.seed = context.state.seed := by
    rw [framed.context_eq]
    exact (configuration_trace path).1
  rw [seed]
  exact GeneralNominalInvocationAncestry.allocation_member _
    (enabled_parent source point ground coverage path enabled) key present
end Yulang.GeneralNominalVersionedInvocationPool237
