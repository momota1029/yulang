import Yulang.GeneralDictionaryBinderProvenance227

/-! Actual-mode current head schema reads no new merge identity. This applies
to the mode-sensitive support used by ReachableRest, not legacy over-approximations. -/
namespace Yulang.GeneralDictionaryHeadFootprint227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227 GeneralDictionaryFootprintCenters227
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
variable {roles : Roles.RoleDecls}

theorem roots_mem
    (trace : Footprint registry context root state pool)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (nonzero : identity ≠ 0)
    (member : identity ∈ List.ofFn plan.input.center ++ [0]) : identity ∈ pool := by
  rcases List.mem_append.mp member with center | zero
  · exact frame_input_centers trace frame center
  · exact False.elim (nonzero (List.mem_singleton.mp zero))

/-- Any fresh non-eight identity in the actual head support was protected
before installation. In particular this excludes first p0/p1 uses here. -/
theorem head_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (notEight : purpose ≠ 8)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalModeFrame181.schemaSources plan plan.headSchema) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool := by
  rcases List.mem_append.mp member with test | usePart
  · obtain ⟨entry,present,equal⟩ := List.mem_map.mp test
    exact roots_mem trace frame GeneralDictionaryBodyProvenance227.fresh_ne_zero
      (equal ▸ (GeneralDictionaryDefault214ActualSupport.head_roots plan).1 entry present)
  · obtain ⟨entry,present,within⟩ := List.mem_flatMap.mp usePart
    have actual := GeneralNominalHeadSchemaNames186.head_actual plan entry present
    simp only [GeneralNominalModeFrame181.variableSources,actual,ite_true,
      List.mem_cons,List.not_mem_nil,or_false] at within
    rcases within with rootEqual | binderEqual
    · exact roots_mem trace frame GeneralDictionaryBodyProvenance227.fresh_ne_zero
        (rootEqual.symm ▸ (GeneralDictionaryDefault214ActualSupport.head_roots plan).2 entry present)
    · exact GeneralDictionaryBinderProvenance227.fresh_binder_mem trace plan frame model valid schema
        (GeneralNominalHeadSchemaNames186.head_input plan entry present) notEight binderEqual.symm

theorem merge_head_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalModeFrame181.schemaSources plan plan.headSchema) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool :=
  head_mem trace plan frame model valid schema (by omega) member

end Yulang.GeneralDictionaryHeadFootprint227
