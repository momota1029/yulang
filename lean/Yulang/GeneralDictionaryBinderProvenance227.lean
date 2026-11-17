import Yulang.GeneralDictionaryPointCaptureSupport227

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryBinderProvenance227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls}

theorem point_singleton (plan : Plan roles)
    (point : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2) :
    ∃ bounds, GeneralNominalAllocation.occurrences plan.packet.bindings name = [bounds] ∧
      (GeneralNominalPacketSupport.capture plan.packet).inputs name = bounds := by
  change (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).1 =
    (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).2 at point
  unfold GeneralNominalAllocation.capture at point
  dsimp only at point
  split at point
  · rename_i bounds equal
    exact ⟨bounds,equal,by change (GeneralNominalAllocation.capture _ _ _ _ _).inputs name = bounds; simp [GeneralNominalAllocation.capture,equal]⟩
  · exact False.elim (GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (0 : Nat) ≠ 1) point)

theorem binder_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (declared : name ∈ plan.packet.declaration.inputNames)
    (nonzero : plan.binder name ≠ 0)
    (notAllocated : plan.binder name ≠ fresh plan.packet.context.state.seed
      plan.packet.site.occurrence.identity plan.packet.declaration.id 8 name 0) :
    plan.binder name ∈ pool := by
  have notOutput := GeneralNominalHeadSchemaNames186.input_not_output plan name declared
  have point : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
    by_cases equal : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2
    · exact equal
    · exact False.elim (notAllocated (by simp [Plan.binder,notOutput,equal]))
  have binder : plan.binder name = ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 := by
    simp [Plan.binder,notOutput,point]
  obtain ⟨bounds,singleton,equal⟩ := point_singleton plan point
  have occurrence : bounds ∈ GeneralNominalAllocation.occurrences plan.packet.bindings name := by simp [singleton]
  obtain ⟨binding,present,boundsEq⟩ := List.mem_map.mp occurrence
  have bindingMem := (List.mem_filter.mp present).1
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings plan] at bindingMem
  obtain ⟨captured,member,bindingEq⟩ := List.mem_map.mp bindingMem
  have lower : plan.packet.context.state.base.source captured.bounds.1 = plan.binder name := by
    rw [binder,equal]
    exact congrArg Prod.fst ((congrArg Prod.snd bindingEq).trans boundsEq)
  have upper : plan.packet.context.state.base.source captured.bounds.2 = plan.binder name := by
    rw [binder,point,equal]
    exact congrArg Prod.snd ((congrArg Prod.snd bindingEq).trans boundsEq)
  obtain ⟨origin,located,_⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured member
  exact GeneralDictionaryPointCaptureSupport227.point_capture_mem trace plan frame model valid schema
    captured member located lower upper nonzero

/-- Input binders from every non-eight fresh namespace, in particular p0/p1,
are already in the old footprint. -/
theorem fresh_binder_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (declared : name ∈ plan.packet.declaration.inputNames)
    (notEight : purpose ≠ 8)
    (equal : plan.binder name = fresh context.state.seed invocation declaration purpose owner position) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool := by
  have seed : plan.packet.context.state.seed = context.state.seed :=
    (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
      (GeneralDictionaryDefaultDepth208.configuration_trace trace.path).1
  rw [← equal]
  apply binder_mem trace plan frame model valid schema declared
  · rw [equal]
    exact GeneralDictionaryBodyProvenance227.fresh_ne_zero
  · rw [equal,seed]
    exact GeneralNominalCenteredAllocation.fresh_namespaces notEight

theorem merge_binder_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (declared : name ∈ plan.packet.declaration.inputNames)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (equal : plan.binder name = fresh context.state.seed invocation declaration purpose owner position) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool :=
  fresh_binder_mem trace plan frame model valid schema declared (by omega) equal

end Yulang.GeneralDictionaryBinderProvenance227
