import Yulang.GeneralNominalVersionedHeadFrame236
import Yulang.GeneralNominalVersionedExpressionFrame236
import Yulang.GeneralNominalSemanticRawFrame236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedPacketFrame236
open GeneralNominalCenters GeneralNominalCommonBridge
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (capture binder childSite)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff captureNames capture_mem)
variable {first last : Assignment}

def privateSources (packet : GeneralNominalSaturationState.Packet roles) : List Nat :=
  GeneralNominalSemanticRawFrame236.sources (privateState packet)
def headSources (packet : GeneralNominalSaturationState.Packet roles) : List Nat :=
  privateSources packet ++ GeneralNominalSemanticRawFrame236.reportSources packet.context.state (GeneralNominalPacketSupport.report packet)

theorem head_models_iff (packet : GeneralNominalSaturationState.Packet roles)
    (same : Agree (headSources packet) first last) : HeadModels packet first ↔ HeadModels packet last :=
  and_congr
    (GeneralNominalSemanticRawFrame236.source_models_same _ (fun name member => same name (List.mem_append_left _ member)))
    (GeneralNominalSemanticRawFrame236.projection_iff _ _ (fun name member => same name (List.mem_append_right _ member)))

def captureSources (plan : Plan roles) : List Nat :=
  (captureNames plan).flatMap fun name => [(capture plan.packet).inputs name |>.1,
    (capture plan.packet).inputs name |>.2,binder plan name]

def childSources (plan : Plan roles) : List Nat :=
  plan.packet.declaration.requirements.attach.flatMap fun clause =>
    let valid := plan.packet.checked.signature.2.2.2 clause.val clause.property
    siteSources (childSite plan clause.val valid) ++
      GeneralNominalVersionedExpressionFrame236.schemaSources plan (childSchema plan clause.val valid)

def sources (plan : Plan roles) : List Nat :=
  headSources plan.packet ++ siteSources plan.input ++ captureSources plan ++
    GeneralNominalVersionedHeadFrame236.schemaSources plan plan.headSchema ++
    GeneralNominalVersionedExpressionFrame236.schemaSources plan (emittedSchema plan) ++ childSources plan

theorem captures_iff (plan : Plan roles) (same : Agree (captureSources plan) first last) (name)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits first ((capture plan.packet).inputs name) (first (binder plan name)).1 ↔
      GeneralNominalCaptureMerges.Fits last ((capture plan.packet).inputs name) (last (binder plan name)).1 := by
  have present := (capture_mem plan name).mpr needed
  have one := same ((capture plan.packet).inputs name).1 (List.mem_flatMap.mpr ⟨name,present,List.mem_cons_self⟩)
  have two := same ((capture plan.packet).inputs name).2 (List.mem_flatMap.mpr ⟨name,present,List.mem_cons_of_mem _ List.mem_cons_self⟩)
  have center := same (binder plan name) (List.mem_flatMap.mpr ⟨name,present,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩)
  unfold GeneralNominalCaptureMerges.Fits
  rw [one,two,center]

theorem children_iff (plan : Plan roles) (same : Agree (childSources plan) first last) :
    (∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
      (childSite plan clause valid).Holds first ∧ (childSchema plan clause valid).Holds (variables plan first) first) ↔
    (∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
      (childSite plan clause valid).Holds last ∧ (childSchema plan clause valid).Holds (variables plan last) last) := by
  apply forall_congr'; intro clause
  apply forall_congr'; intro member
  apply forall_congr'; intro valid
  have inner : Agree (siteSources (childSite plan clause valid) ++
      GeneralNominalVersionedExpressionFrame236.schemaSources plan (childSchema plan clause valid)) first last := by
    intro name present
    exact same name (List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,present⟩)
  exact and_congr (site_iff _ (fun name member => inner name (List.mem_append_left _ member)))
    (GeneralNominalVersionedExpressionFrame236.schema_iff _ _ (fun name member => inner name (List.mem_append_right _ member)))

theorem holds_shape (plan : Plan roles) (model : Assignment) : Holds plan model ↔
    HeadModels plan.packet model ∧ plan.input.Holds model ∧
    (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
      GeneralNominalCaptureMerges.Fits model ((capture plan.packet).inputs name) (model (binder plan name)).1) ∧
    SchemaHolds plan plan.headSchema model ∧
    (∀ equation ∈ (emittedSchema plan).equations, equation.mode ≠ .actual → equation.Holds (variables plan model) model) ∧
    (∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
      (childSite plan clause valid).Holds model ∧ (childSchema plan clause valid).Holds (variables plan model) model) ∧
    Outputs plan model := by
  simp only [Holds,Inputs,HeadModels,private_models_iff,and_assoc]

theorem holds_iff (plan : Plan roles) (same : Agree (sources plan) first last) : Holds plan first ↔ Holds plan last := by
  rw [holds_shape,holds_shape]
  apply and_congr (head_models_iff plan.packet (fun n h => same n (by simp [sources,h])))
  apply and_congr (site_iff plan.input (fun n h => same n (by simp [sources,h])))
  apply and_congr
  · apply forall_congr'; intro name
    apply forall_congr'; intro needed
    exact captures_iff plan (fun n h => same n (by simp [sources,h])) name needed
  apply and_congr (GeneralNominalVersionedHeadFrame236.schema_iff plan plan.headSchema
    (fun n h => same n (by simp [sources,h])))
  apply and_congr
  · apply forall_congr'; intro equation
    apply forall_congr'; intro member
    apply forall_congr'; intro _
    apply GeneralNominalVersionedExpressionFrame236.equation_iff
    intro name present
    have named : name ∈ GeneralNominalVersionedExpressionFrame236.schemaSources plan (emittedSchema plan) :=
      List.mem_flatMap.mpr ⟨equation,member,present⟩
    exact same name (by simp [sources,named])
  exact and_congr (children_iff plan (fun n h => same n (by simp [sources,h])))
    (GeneralNominalVersionedExpressionFrame236.schema_iff plan (emittedSchema plan)
      (fun n h => same n (by simp [sources,h])))
end Yulang.GeneralNominalVersionedPacketFrame236
