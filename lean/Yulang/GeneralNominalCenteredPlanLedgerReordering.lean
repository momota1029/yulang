import Yulang.GeneralNominalCenteredLedgerPermutation

set_option backward.isDefEq.respectTransparency false

/-! Existing plan rebasing supplies the separated input/output equations used
by the centered trusted ledger, in addition to the full plan equations. -/
namespace Yulang.GeneralNominalCenteredPlanLedgerReordering
open GeneralDeclarations GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredPlanReordering
variable {roles : Roles.RoleDecls} {original : Plan roles} {registry : Registry} {declaration : Declaration}

theorem inputs (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (model) :
    GeneralNominalCenteredSupport.Inputs (rebase original order pair) model ↔ GeneralNominalCenteredSupport.Inputs original model := by
  have cap : GeneralNominalPacketSupport.capture (rebase original order pair).packet = GeneralNominalPacketSupport.capture original.packet :=
    GeneralNominalPacketReordering.capture order pair
  have inp : GeneralNominalPacketSupport.inputSchema (rebase original order pair).packet = GeneralNominalPacketSupport.inputSchema original.packet :=
    GeneralNominalPacketReordering.input_schema order pair
  have packet : GeneralNominalPacketSupport.Inputs (rebase original order pair).packet model ↔ GeneralNominalPacketSupport.Inputs original.packet model :=
    GeneralNominalPacketReordering.inputs order pair model
  unfold GeneralNominalCenteredSupport.Inputs
  simp only [packet,needed,binder,head_schema,cap,inp,schema_holds,child_requests,child_site]
  change (_ ∧ original.input.Holds model ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
  simp only [Plan.schema,rebase,GeneralNominalPacketReordering.rebase,Declaration.inputNames,pair.head]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact forall_congr' (fun clause => imp_congr pair.requirements.mem_iff.symm Iff.rfl)

theorem outputs (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (roleEq : original.packet.registry.roles = roles) (model) :
    GeneralNominalCenteredSupport.Outputs (rebase original order pair) model ↔ GeneralNominalCenteredSupport.Outputs original model := by
  have out : GeneralNominalPacketSupport.namedSchema (rebase original order pair).packet = GeneralNominalPacketSupport.namedSchema original.packet :=
    GeneralNominalPacketReordering.named_schema order pair roleEq
  have packet : GeneralNominalPacketSupport.Outputs (rebase original order pair).packet model ↔ GeneralNominalPacketSupport.Outputs original.packet model :=
    GeneralNominalPacketReordering.outputs order pair roleEq model
  simp only [GeneralNominalCenteredSupport.Outputs,out,packet,schema_holds]

theorem paired (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (roleEq : original.packet.registry.roles = roles)
    {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    (recorded : relation original.packet (rebase original order pair).packet) :
    GeneralNominalCenteredLedgerPermutation.PlanPair relation original (rebase original order pair) :=
  ⟨recorded,rfl,fun model => (inputs order pair model).symm,fun model => (outputs order pair roleEq model).symm,
    fun model => (equations order pair roleEq model).symm,fun entry => (tests_mem order pair roleEq entry).symm⟩

end Yulang.GeneralNominalCenteredPlanLedgerReordering
