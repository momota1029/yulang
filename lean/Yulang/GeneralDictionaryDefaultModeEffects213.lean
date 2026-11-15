import Yulang.GeneralDictionaryDefaultModeSupport213

/-! Mode-sensitive total default/explicit effects and live class frames. -/
namespace Yulang.GeneralDictionaryDefaultModeEffects213
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatSchemas (Schema)
open GeneralNominalCenteredHeadMatExtension (sources)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefaultTotalFrame212 (resolve variables_sources bodyResolve body_variables_sources)
open GeneralDictionaryDefaultModeSupport213 (schemaSources schema_iff)
variable {roles : Roles.RoleDecls} {first last : Assignment}
 theorem plan_schema_iff (plan : Plan roles) (schema : Schema)
    (same : Agree (schemaSources (resolve plan) schema) first last) :
    schema.Holds (variables plan first) first ↔ schema.Holds (variables plan last) last := by
  rw [variables_sources,variables_sources]
  exact schema_iff _ _ same

 def bodySources (plan : Plan roles) (target : Nat) (body : GeneralDictionaryAssociatedProvenance.Body) : List Nat :=
  schemaSources (bodyResolve plan body) (bodySchema plan target body)

 theorem body_iff (plan : Plan roles) (target : Nat) (body)
    (same : Agree (bodySources plan target body) first last) :
    BodyHolds plan target first body ↔ BodyHolds plan target last body := by
  unfold BodyHolds
  rw [body_variables_sources,body_variables_sources]
  exact schema_iff _ _ same

 noncomputable def classSources (state : GeneralNominalCenteredSteps.State roles)
    (focus : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) : List Nat :=
  (GeneralNominalCenteredHeadOutputs.requests state focus).flatMap fun output =>
    output.target :: ((GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name).toList.flatMap
      fun body => bodySources plan output.target body)

 theorem class_iff (state : GeneralNominalCenteredSteps.State roles)
    (focus : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles)
    (same : Agree (classSources state focus plan) first last) :
    ClassEffects state focus plan first ↔ ClassEffects state focus plan last := by
  have target output (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state focus) :
      first output.target = last output.target :=
    same _ (List.mem_flatMap.mpr ⟨output,member,List.mem_cons_self ..⟩)
  unfold ClassEffects
  apply and_congr
  · apply forall_congr'; intro output
    apply forall_congr'; intro member
    apply forall_congr'; intro body
    apply forall_congr'; intro found
    apply body_iff
    intro name present
    apply same
    apply List.mem_flatMap.mpr
    refine ⟨output,member,List.mem_cons_of_mem _ ?_⟩
    exact List.mem_flatMap.mpr ⟨body,Option.mem_toList.mpr found,present⟩
  · unfold GeneralNominalCenteredHeadOutputs.EqualOutputs
    apply forall_congr'; intro a
    apply forall_congr'; intro aMember
    apply forall_congr'; intro b
    apply forall_congr'; intro bMember
    rw [target a aMember,target b bMember]

end Yulang.GeneralDictionaryDefaultModeEffects213
