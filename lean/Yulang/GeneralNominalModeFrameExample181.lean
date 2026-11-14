import Yulang.GeneralNominalModeFrame181
import Yulang.GeneralDictionaryCenteredNominalPointExample178

/-! A nonactual schema can ignore a binder listed by the old frame. Changing
that binder preserves this schema, not the full plan or centered journal. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalModeFrameExample181
open GeneralNominalCenters GeneralNominalRecursiveInspection GeneralNominalMaterialization
open CommonNominalFullCarrier
open GeneralDictionaryCenteredNominalPointExample178 (plan)
open GeneralDictionaryNominalPairExample178 (assignment)

 def entry : Use := ⟨0,.source 3,.upper⟩
 def schema : Schema := ⟨[entry],[],false⟩

 theorem binder_outside : plan.binder 0 ∉ GeneralNominalModeFrame181.schemaSources plan schema := by
  decide +kernel

 theorem binder_inside_old : plan.binder 0 ∈ GeneralNominalCenteredFrame179.schemaSources plan schema := by
  simp [GeneralNominalCenteredFrame179.schemaSources,GeneralNominalCenteredFrame179.variableSources,schema,entry]

 def changed : GeneralNominalCommonBridge.Assignment := fun name =>
  if name = plan.binder 0 then (.bottom,Common.rowEmpty) else assignment false name

 theorem agreement : GeneralNominalCenteredFrame179.Agree
    (GeneralNominalModeFrame181.schemaSources plan schema) (assignment false) changed := by
  intro name member
  have different : name ≠ plan.binder 0 := by
    intro equal
    subst name
    exact binder_outside member
  simp only [changed,different,ite_false]

 theorem old_holds : plan.SchemaHolds schema (assignment false) := by
  constructor
  · intro test member
    cases member
  · intro use member
    have equal : use = entry := List.mem_singleton.mp member
    subst use
    have endpoints : (GeneralNominalPacketSupport.capture plan.packet).inputs 0 = (2,3) := by decide +kernel
    have notOutput : 0 ∉ plan.packet.declaration.outputNames := by decide +kernel
    simp only [entry,reduceCtorEq,ite_false,VariableHolds,notOutput,endpoints]
    change (∃ value, Observes (assignment false) (.source 3) value) ∧
      ∀ value, Observes (assignment false) (.source 3) value →
        Equivalent value (assignment false 3).1
    refine ⟨⟨_,.source 3⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨subtype_refl _,subtype_refl _⟩

 theorem changed_holds : plan.SchemaHolds schema changed :=
  (GeneralNominalModeFrame181.schema_iff plan schema agreement).mp old_holds

 theorem old_binder_top : (assignment false (plan.binder 0)).1 = .top := by
  have exactName : plan.binder 0 = 29485004 := by decide +kernel
  rw [exactName]
  rfl

 theorem changed_binder_bottom : (changed (plan.binder 0)).1 = .bottom := by
  simp only [changed,ite_true]

 theorem old_frame_disagrees : ¬ GeneralNominalCenteredFrame179.Agree
    (GeneralNominalCenteredFrame179.schemaSources plan schema) (assignment false) changed := by
  intro same
  have values := congrArg Prod.fst (same _ binder_inside_old)
  rw [old_binder_top,changed_binder_bottom] at values
  cases values

end Yulang.GeneralNominalModeFrameExample181
