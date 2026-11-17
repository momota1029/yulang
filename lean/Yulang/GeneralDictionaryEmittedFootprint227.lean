import Yulang.GeneralDictionaryFirstPacketTail227
import Yulang.GeneralDictionaryDefault214ActualTotalSources

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryEmittedFootprint227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
variable {roles : Roles.RoleDecls}

theorem nonoutput_binder_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (notOutput : name ∉ plan.packet.declaration.outputNames)
    (nonzero : plan.binder name ≠ 0)
    (notAllocated : plan.binder name ≠ fresh plan.packet.context.state.seed
      plan.packet.site.occurrence.identity plan.packet.declaration.id 8 name 0) :
    plan.binder name ∈ pool := by
  have point : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
    by_cases equal : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2
    · exact equal
    · exact False.elim (notAllocated (by simp [Plan.binder,notOutput,equal]))
  have binder : plan.binder name = ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 := by
    simp [Plan.binder,notOutput,point]
  obtain ⟨bounds,singleton,equal⟩ := GeneralDictionaryBinderProvenance227.point_singleton plan point
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

/-- Even a syntactically unscoped name cannot introduce a p0/p1 actual binder.
A non-output point binder has an actual captured singleton witness. -/
theorem any_binder_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (notTwo : purpose ≠ 2) (notEight : purpose ≠ 8)
    (equal : plan.binder name = fresh context.state.seed invocation declaration purpose owner position) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool := by
  have seed : plan.packet.context.state.seed = context.state.seed :=
    (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
      (GeneralDictionaryDefaultDepth208.configuration_trace trace.path).1
  have notOutput : name ∉ plan.packet.declaration.outputNames := by
    intro declared
    have separate := GeneralDictionaryBodyProvenance227.output_separate (invocation := invocation) (declaration := declaration) (owner := owner) (position := position) plan notTwo declared
    rw [seed] at separate
    exact separate equal.symm
  rw [← equal]
  apply nonoutput_binder_mem trace plan frame model valid schema notOutput
  · rw [equal]; exact GeneralDictionaryBodyProvenance227.fresh_ne_zero
  · rw [equal,seed]; exact GeneralNominalCenteredAllocation.fresh_namespaces notEight

theorem actual_reads_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (notTwo : purpose ≠ 2) (notEight : purpose ≠ 8)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryDefaultModeSupport212.reads (resolve plan) .actual expression) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool := by
  rw [GeneralDictionaryDefaultModeSupport213.actual_reads] at member
  obtain ⟨name,_,equal⟩ := List.mem_map.mp member
  have binder : plan.binder name = fresh context.state.seed invocation declaration purpose owner position := by
    simpa only [resolve,ite_self] using equal
  exact any_binder_mem trace plan frame model valid schema notTwo notEight binder

/-- For any total schema, actual RHS reads are old. Only targets or explicitly
lower/upper-mode equations remain; this does not remove emitted input ranges. -/
theorem schema_residual
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (head : plan.SchemaHolds plan.headSchema model)
    (notTwo : purpose ≠ 2) (notEight : purpose ≠ 8)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryDefaultModeSupport213.schemaSources (resolve plan) schema) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool ∨
    ∃ equation ∈ schema.equations,
      fresh context.state.seed invocation declaration purpose owner position = equation.target ∨
      (equation.mode ≠ .actual ∧ fresh context.state.seed invocation declaration purpose owner position ∈
        GeneralDictionaryDefaultModeSupport212.reads (resolve plan) equation.mode equation.expression) := by
  obtain ⟨equation,present,within⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp within with target | read
  · exact Or.inr ⟨equation,present,Or.inl target⟩
  · by_cases actual : equation.mode = .actual
    · rw [actual] at read
      exact Or.inl (actual_reads_mem trace plan frame model valid head notTwo notEight read)
    · exact Or.inr ⟨equation,present,Or.inr ⟨actual,read⟩⟩

end Yulang.GeneralDictionaryEmittedFootprint227
