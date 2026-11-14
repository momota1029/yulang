import Yulang.GeneralNominalCenteredFrame179

/-! Schema support follows the use mode. Actual uses read the origin and binder;
endpoint uses read the origin and capture names, not an extra centered binder.
No satisfiability or reachability hypothesis is needed for this frame. -/
namespace Yulang.GeneralNominalModeFrame181
open GeneralNominalCenters GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCenteredFrame179 (Agree observes_iff head_iff same_iff)

variable {first last : Assignment}

 def variableSources (plan : Plan roles) (entry : Use) : List Nat :=
  if entry.mode = .actual then [originSource entry.origin,plan.binder entry.name]
  else [originSource entry.origin,
    (GeneralNominalPacketSupport.capture plan.packet).outputs entry.name,
    ((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).1,
    ((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).2]

 def schemaSources (plan : Plan roles) (schema : Schema) : List Nat :=
  schema.tests.map (fun test => originSource test.1) ++ schema.variables.flatMap (variableSources plan)

 theorem schema_iff (plan : Plan roles) (schema : Schema)
    (same : Agree (schemaSources plan schema) first last) :
    plan.SchemaHolds schema first ↔ plan.SchemaHolds schema last := by
  have tests entry (member : entry ∈ schema.tests) :
      GeneralNominalOriginTerms.Head first entry.1 entry.2 ↔ GeneralNominalOriginTerms.Head last entry.1 entry.2 :=
    head_iff _ _ (same _ (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)))
  have variables entry (member : entry ∈ schema.variables) :
      Agree (variableSources plan entry) first last := by
    intro name present
    exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,member,present⟩))
  unfold Plan.SchemaHolds
  apply and_congr
  · exact forall_congr' fun entry => forall_congr' fun member => tests entry member
  · apply forall_congr'; intro entry
    apply forall_congr'; intro member
    have support := variables entry member
    have root := support (originSource entry.origin) (by
      unfold variableSources
      split <;> simp)
    by_cases actual : entry.mode = .actual
    · simp only [actual,ite_true]
      exact same_iff _ _ root (support (plan.binder entry.name) (by simp [variableSources,actual]))
    · simp only [actual,ite_false]
      have output := support ((GeneralNominalPacketSupport.capture plan.packet).outputs entry.name)
        (by simp [variableSources,actual])
      have lower := support (((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).1)
        (by simp [variableSources,actual])
      have upper := support (((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).2)
        (by simp [variableSources,actual])
      simp only [observes_iff entry.origin root,VariableHolds,GeneralNominalCaptureMerges.Fits,output,lower,upper]

 theorem variableSources_subset (plan : Plan roles) (entry : Use) :
    variableSources plan entry ⊆ GeneralNominalCenteredFrame179.variableSources plan entry := by
  intro name present
  by_cases actual : entry.mode = .actual
  · simp only [variableSources,actual,ite_true,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl <;> simp [GeneralNominalCenteredFrame179.variableSources]
  · simp only [variableSources,actual,ite_false,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl | rfl <;> simp [GeneralNominalCenteredFrame179.variableSources]

 theorem schemaSources_subset (plan : Plan roles) (schema : Schema) :
    schemaSources plan schema ⊆ GeneralNominalCenteredFrame179.schemaSources plan schema := by
  intro name present
  rcases List.mem_append.mp present with test | useMember
  · exact List.mem_append_left _ test
  · obtain ⟨entry,member,within⟩ := List.mem_flatMap.mp useMember
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨entry,member,variableSources_subset plan entry within⟩)

 theorem nonactual_singleton_iff (plan : Plan roles) (entry : Use)
    (nonactual : entry.mode ≠ .actual)
    (same : Agree [originSource entry.origin,
      (GeneralNominalPacketSupport.capture plan.packet).outputs entry.name,
      ((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).1,
      ((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).2] first last) :
    plan.SchemaHolds ⟨[entry],[],false⟩ first ↔ plan.SchemaHolds ⟨[entry],[],false⟩ last := by
  apply schema_iff
  simpa only [schemaSources,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.nil_append,variableSources,nonactual,ite_false] using same

end Yulang.GeneralNominalModeFrame181
