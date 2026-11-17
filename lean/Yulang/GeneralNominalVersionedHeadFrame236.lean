import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalCenteredFrame179

/-! Schema support follows the use mode. Actual uses read the origin and binder;
endpoint uses read the origin and capture names, not an extra centered binder.
No satisfiability or reachability hypothesis is needed for this frame. -/
namespace Yulang.GeneralNominalVersionedHeadFrame236
open GeneralNominalCenters GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCenteredFrame179 (Agree observes_iff head_iff same_iff)

variable {first last : Assignment}

 def variableSources (plan : Plan roles) (entry : Use) : List Nat :=
  if entry.mode = .actual then [originSource entry.origin,GeneralNominalVersionedFrame231.binder plan entry.name]
  else [originSource entry.origin,
    (GeneralNominalVersionedFrame231.capture plan.packet).outputs entry.name,
    ((GeneralNominalVersionedFrame231.capture plan.packet).inputs entry.name).1,
    ((GeneralNominalVersionedFrame231.capture plan.packet).inputs entry.name).2]

 def schemaSources (plan : Plan roles) (schema : Schema) : List Nat :=
  schema.tests.map (fun test => originSource test.1) ++ schema.variables.flatMap (variableSources plan)

 theorem schema_iff (plan : Plan roles) (schema : Schema)
    (same : Agree (schemaSources plan schema) first last) :
    GeneralNominalVersionedPlans231.SchemaHolds plan schema first ↔ GeneralNominalVersionedPlans231.SchemaHolds plan schema last := by
  have tests entry (member : entry ∈ schema.tests) :
      GeneralNominalOriginTerms.Head first entry.1 entry.2 ↔ GeneralNominalOriginTerms.Head last entry.1 entry.2 :=
    head_iff _ _ (same _ (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)))
  have variables entry (member : entry ∈ schema.variables) :
      Agree (variableSources plan entry) first last := by
    intro name present
    exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,member,present⟩))
  unfold GeneralNominalVersionedPlans231.SchemaHolds
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
      exact same_iff _ _ root (support (GeneralNominalVersionedFrame231.binder plan entry.name) (by simp [variableSources,actual]))
    · simp only [actual,ite_false]
      have output := support ((GeneralNominalVersionedFrame231.capture plan.packet).outputs entry.name)
        (by simp [variableSources,actual])
      have lower := support (((GeneralNominalVersionedFrame231.capture plan.packet).inputs entry.name).1)
        (by simp [variableSources,actual])
      have upper := support (((GeneralNominalVersionedFrame231.capture plan.packet).inputs entry.name).2)
        (by simp [variableSources,actual])
      simp only [observes_iff entry.origin root,VariableHolds,GeneralNominalCaptureMerges.Fits,output,lower,upper]


end Yulang.GeneralNominalVersionedHeadFrame236
