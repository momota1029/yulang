import Yulang.GeneralNominalCenteredPermutationContext

set_option backward.isDefEq.respectTransparency false

/-! New plans retain the input center while their packet is moved onto the
counterpart's current metadata enumeration. -/
namespace Yulang.GeneralNominalCenteredPermutationPlans
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalMetadataEquivalence (replace)
variable {roles : Roles.RoleDecls}

def metadata (plan : Plan roles) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat) : Plan roles :=
  ⟨GeneralNominalPacketMetadata.rebase plan.packet allocated reserved,plan.input,plan.input_exact⟩

variable (plan : Plan roles) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

theorem binder (name) : (metadata plan allocated reserved).binder name = plan.binder name := by
  unfold Plan.binder
  simp only [metadata,GeneralNominalPacketMetadata.capture]
  rfl

theorem head_schema : (metadata plan allocated reserved).headSchema = plan.headSchema := rfl

theorem schema (requests) : (metadata plan allocated reserved).schema requests = plan.schema requests := rfl

theorem schema_holds (schema model) : (metadata plan allocated reserved).SchemaHolds schema model ↔ plan.SchemaHolds schema model := by
  unfold Plan.SchemaHolds
  simp only [binder]
  dsimp only [metadata]
  rw [GeneralNominalPacketMetadata.capture]
  rfl

theorem emitted_center (clause position pattern) : (metadata plan allocated reserved).emittedCenter clause position pattern = plan.emittedCenter clause position pattern := by
  unfold Plan.emittedCenter
  split
  · exact binder ..
  · rfl

theorem clause_child (clause : Clause) (valid : clause.Signature roles) :
    GeneralNominalFeedbackSites.clauseChild (metadata plan allocated reserved).packet clause valid =
      GeneralNominalFeedbackSites.clauseChild plan.packet clause valid := by
  unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame
  simp only [metadata,GeneralNominalPacketMetadata.bindings]
  rfl

theorem child_site (clause : Clause) (valid : clause.Signature roles) :
    (metadata plan allocated reserved).childSite clause valid = plan.childSite clause valid := by
  unfold Plan.childSite
  congr 1
  · exact clause_child ..
  · funext index
    exact emitted_center ..

theorem child_requests (clause : Clause) (valid : clause.Signature roles) :
    (metadata plan allocated reserved).childRequests clause valid = plan.childRequests clause valid := by
  simp only [Plan.childRequests,Plan.childSite,emitted_center]

theorem inputs (model) : GeneralNominalCenteredSupport.Inputs (metadata plan allocated reserved) model ↔
    GeneralNominalCenteredSupport.Inputs plan model := by
  have cap : GeneralNominalPacketSupport.capture (metadata plan allocated reserved).packet = GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketMetadata.capture ..
  have inp : GeneralNominalPacketSupport.inputSchema (metadata plan allocated reserved).packet = GeneralNominalPacketSupport.inputSchema plan.packet := GeneralNominalPacketMetadata.input_schema ..
  have packet : GeneralNominalPacketSupport.Inputs (metadata plan allocated reserved).packet model ↔ GeneralNominalPacketSupport.Inputs plan.packet model := GeneralNominalPacketMetadata.inputs ..
  simp only [GeneralNominalCenteredSupport.Inputs,packet,cap,inp,binder,head_schema,schema_holds,child_site,child_requests,schema]
  rfl

theorem outputs (model) : GeneralNominalCenteredSupport.Outputs (metadata plan allocated reserved) model ↔
    GeneralNominalCenteredSupport.Outputs plan model := by
  have out : GeneralNominalPacketSupport.namedSchema (metadata plan allocated reserved).packet = GeneralNominalPacketSupport.namedSchema plan.packet := GeneralNominalPacketMetadata.named_schema ..
  have packet : GeneralNominalPacketSupport.Outputs (metadata plan allocated reserved).packet model ↔ GeneralNominalPacketSupport.Outputs plan.packet model := GeneralNominalPacketMetadata.outputs ..
  simp only [GeneralNominalCenteredSupport.Outputs,packet,out,schema_holds]

theorem equations (model) : (metadata plan allocated reserved).Equations model ↔ plan.Equations model := by
  have cap : GeneralNominalPacketSupport.capture (metadata plan allocated reserved).packet = GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketMetadata.capture ..
  have inp : GeneralNominalPacketSupport.inputSchema (metadata plan allocated reserved).packet = GeneralNominalPacketSupport.inputSchema plan.packet := GeneralNominalPacketMetadata.input_schema ..
  have out : GeneralNominalPacketSupport.namedSchema (metadata plan allocated reserved).packet = GeneralNominalPacketSupport.namedSchema plan.packet := GeneralNominalPacketMetadata.named_schema ..
  simp only [Plan.Equations,cap,inp,out,binder,head_schema,schema_holds,child_site,child_requests,schema]
  rfl

theorem holds (model) : (metadata plan allocated reserved).Holds model ↔ plan.Holds model :=
  and_congr (GeneralNominalPacketMetadata.holds ..) (equations ..)

theorem emitted : (metadata plan allocated reserved).emitted = plan.emitted := by
  simp only [Plan.emitted,child_site]
  rfl

theorem tests : GeneralNominalCenteredSteps.Plan.tests (metadata plan allocated reserved) = GeneralNominalCenteredSteps.Plan.tests plan := by
  have out : GeneralNominalPacketSupport.namedSchema (metadata plan allocated reserved).packet = GeneralNominalPacketSupport.namedSchema plan.packet := GeneralNominalPacketMetadata.named_schema ..
  simp only [GeneralNominalCenteredSteps.Plan.tests,head_schema,out,child_requests,schema]
  rfl

theorem inspection : GeneralNominalCenteredSteps.inspection (metadata plan allocated reserved) =
    GeneralNominalReportMetadata.report plan.packet.context.state allocated reserved (GeneralNominalCenteredSteps.inspection plan) := by
  unfold GeneralNominalCenteredSteps.inspection
  dsimp only [metadata,GeneralNominalPacketMetadata.rebase]
  rw [GeneralNominalMetadataInspection.queries]
  exact (GeneralNominalReportMetadata.many ..).symm

theorem paired {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    (recorded : relation plan.packet (metadata plan allocated reserved).packet) :
    GeneralNominalCenteredLedgerPermutation.PlanPair relation plan (metadata plan allocated reserved) :=
  ⟨recorded,rfl,fun model => (inputs ..).symm,fun model => (outputs ..).symm,
    fun model => (equations ..).symm,fun entry => by rw [tests]⟩

end Yulang.GeneralNominalCenteredPermutationPlans
