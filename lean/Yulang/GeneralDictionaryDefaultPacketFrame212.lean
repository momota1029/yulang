import Yulang.GeneralDictionaryDefaultTotalFrame212
import Yulang.GeneralNominalRawFrame179

/-! Finite support for the actual total-packet meaning, including all child
schemas. No syntactic partial materializer is substituted for total Holds. -/
namespace Yulang.GeneralDictionaryDefaultPacketFrame212
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff captureSources capture_mem)
open GeneralDictionaryDefaultTotalFrame212 (resolve schemaSources plan_schema_iff)
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
variable {roles : Roles.RoleDecls} {first last : Assignment}

 def headSources (plan : Plan roles) : List Nat :=
  GeneralNominalState.sources plan.packet.privateContext.state ++
    GeneralNominalRawFrame179.reportSources plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)

 theorem head_iff (plan : Plan roles) (same : Agree (headSources plan) first last) :
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds first ↔
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds last := by
  have raw : Agree (GeneralNominalState.sources plan.packet.privateContext.state) first last :=
    fun name member => same name (List.mem_append_left _ member)
  apply and_congr
  · exact ⟨GeneralNominalCenteredModelExtension.source_models_same _ raw,
      GeneralNominalCenteredModelExtension.source_models_same _ (fun name member => (raw name member).symm)⟩
  · exact GeneralNominalRawFrame179.projection_iff _ _
      (fun name member => same name (List.mem_append_right _ member))

 theorem fits_iff (plan : Plan roles) (same : Agree (captureSources plan) first last) :
    (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
      GeneralNominalCaptureMerges.Fits first ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
        (first (plan.binder name)).1) ↔
    (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
      GeneralNominalCaptureMerges.Fits last ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
        (last (plan.binder name)).1) := by
  apply forall_congr'; intro name
  apply forall_congr'; intro needed
  have member := (capture_mem plan name).mpr needed
  have one := same (((GeneralNominalPacketSupport.capture plan.packet).inputs name).1)
    (List.mem_flatMap.mpr ⟨name,member,by simp⟩)
  have two := same (((GeneralNominalPacketSupport.capture plan.packet).inputs name).2)
    (List.mem_flatMap.mpr ⟨name,member,by simp⟩)
  have center := same (plan.binder name) (List.mem_flatMap.mpr ⟨name,member,by simp⟩)
  simp only [GeneralNominalCaptureMerges.Fits,one,two,center]

 def childSources (plan : Plan roles) : List Nat :=
  plan.packet.declaration.requirements.attach.flatMap fun clause =>
    let valid := plan.packet.checked.signature.2.2.2 clause.val clause.property
    siteSources (plan.childSite clause.val valid) ++ schemaSources (resolve plan) (childSchema plan clause.val valid)

 def packetSources (plan : Plan roles) : List Nat :=
  headSources plan ++ siteSources plan.input ++ captureSources plan ++
    GeneralNominalModeFrame181.schemaSources plan plan.headSchema ++
    schemaSources (resolve plan) (emittedSchema plan) ++ childSources plan

 theorem packet_iff (plan : Plan roles) (same : Agree (packetSources plan) first last) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan first ↔
    GeneralNominalCenteredHeadMatStepPackets.Holds plan last := by
  rw [← GeneralNominalCenteredHeadMatStepPackets.models_iff,← GeneralNominalCenteredHeadMatStepPackets.models_iff]
  unfold GeneralNominalCenteredHeadMatPlans.Models
  apply and_congr (head_iff plan (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (site_iff plan.input (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (fits_iff plan (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (GeneralNominalModeFrame181.schema_iff plan plan.headSchema
    (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (plan_schema_iff plan (emittedSchema plan)
    (fun name member => same name (by simp [packetSources,member])))
  apply forall_congr'; intro clause
  apply forall_congr'; intro member
  apply forall_congr'; intro valid
  have support : Agree (siteSources (plan.childSite clause valid) ++
      schemaSources (resolve plan) (childSchema plan clause valid)) first last := by
    intro name present
    apply same
    have contained : name ∈ childSources plan :=
      List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,present⟩
    simp [packetSources,contained]
  exact and_congr (site_iff _ (fun name member => support name (List.mem_append_left _ member)))
    (plan_schema_iff _ _ (fun name member => support name (List.mem_append_right _ member)))

end Yulang.GeneralDictionaryDefaultPacketFrame212
