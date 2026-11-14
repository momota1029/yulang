import Yulang.GeneralNominalReportMetadata
import Yulang.GeneralNominalLedgerPermutation

set_option backward.isDefEq.respectTransparency false

/-! Packet rebasing across metadata-related current contexts preserves every
observation consumed by legacy and centered support ledgers. -/
namespace Yulang.GeneralNominalPacketMetadata
open GeneralNominalSaturationState (Packet)
open GeneralNominalMetadataEquivalence (replace)
variable {roles : Roles.RoleDecls}

def rebase (packet : Packet roles) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat) : Packet roles :=
  ⟨packet.registry,⟨replace packet.context.state allocated reserved,packet.context.interpretation⟩,
    packet.site,packet.declaration,packet.checked,packet.bounds⟩

variable (packet : Packet roles) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

theorem report : GeneralNominalPacketSupport.report (rebase packet allocated reserved) =
    GeneralNominalReportMetadata.report packet.context.state allocated reserved (GeneralNominalPacketSupport.report packet) := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  dsimp only [rebase]
  rw [GeneralNominalMetadataInspection.queries,← GeneralNominalReportMetadata.many]
  rfl

theorem bindings : (rebase packet allocated reserved).bindings = packet.bindings := by
  unfold Packet.bindings
  change GeneralNominalRecursiveInspection.bindings _ (GeneralNominalPacketSupport.report _) = _
  rw [report]
  exact GeneralNominalReportMetadata.bindings ..

theorem capture : GeneralNominalPacketSupport.capture (rebase packet allocated reserved) =
    GeneralNominalPacketSupport.capture packet := by
  unfold GeneralNominalPacketSupport.capture
  rw [bindings]
  rfl

theorem children : (rebase packet allocated reserved).children = packet.children := by
  unfold Packet.children
  rw [bindings]
  rfl

theorem named_schema : GeneralNominalPacketSupport.namedSchema (rebase packet allocated reserved) =
    GeneralNominalPacketSupport.namedSchema packet := by
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
  change GeneralNominalMaterialization.generated _ _ (GeneralNominalMaterialization.requests _ _ _ _ _ (rebase packet allocated reserved).bindings) =
    GeneralNominalMaterialization.generated _ _ (GeneralNominalMaterialization.requests _ _ _ _ _ packet.bindings)
  rw [bindings]
  rfl

theorem input_schema : GeneralNominalPacketSupport.inputSchema (rebase packet allocated reserved) =
    GeneralNominalPacketSupport.inputSchema packet := by
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  rw [capture]
  rfl

theorem ordinary (model) : GeneralNominalPacketSupport.Ordinary (rebase packet allocated reserved) model ↔
    GeneralNominalPacketSupport.Ordinary packet model := by
  unfold GeneralNominalPacketSupport.Ordinary
  rw [bindings,report]
  rfl

theorem materialization (schema model) :
    GeneralNominalMaterialization.Models (rebase packet allocated reserved).context.state packet.declaration
      (GeneralNominalPacketSupport.capture packet) (GeneralNominalPacketSupport.report (rebase packet allocated reserved)) schema model ↔
    GeneralNominalMaterialization.Models packet.context.state packet.declaration
      (GeneralNominalPacketSupport.capture packet) (GeneralNominalPacketSupport.report packet) schema model := by
  rw [report]
  simp only [GeneralNominalMaterialization.Models,GeneralNominalReportMetadata.report,List.forall_mem_map,
    GeneralNominalReportMetadata.capture]

theorem inputs (model) : GeneralNominalPacketSupport.Inputs (rebase packet allocated reserved) model ↔
    GeneralNominalPacketSupport.Inputs packet model := by
  unfold GeneralNominalPacketSupport.Inputs
  rw [ordinary,input_schema,capture]
  change (_ ∧ _ ∧ GeneralNominalMaterialization.Models _ packet.declaration _ _ _ _) ↔ _
  rw [materialization,report]
  exact and_congr Iff.rfl (and_congr (GeneralNominalReportMetadata.projectionModels ..) Iff.rfl)

theorem outputs (model) : GeneralNominalPacketSupport.Outputs (rebase packet allocated reserved) model ↔
    GeneralNominalPacketSupport.Outputs packet model := by
  unfold GeneralNominalPacketSupport.Outputs
  rw [named_schema,capture]
  exact materialization packet allocated reserved _ model

theorem holds (model) : (rebase packet allocated reserved).Holds model ↔ packet.Holds model := by
  rw [GeneralNominalPacketSupport.packet_exact,GeneralNominalPacketSupport.packet_exact,inputs,outputs]
  rfl

theorem inherited_report : GeneralNominalSharedCaptures.inheritedReport (rebase packet allocated reserved) =
    GeneralNominalReportMetadata.report packet.context.state allocated reserved (GeneralNominalSharedCaptures.inheritedReport packet) := by
  unfold GeneralNominalSharedCaptures.inheritedReport
  dsimp only [rebase]
  rw [GeneralNominalMetadataInspection.queries]
  exact (GeneralNominalReportMetadata.many ..).symm

theorem observation : GeneralNominalLedgerPermutation.PacketObservation packet (rebase packet allocated reserved) := by
  refine ⟨⟨rfl,(children packet allocated reserved).symm,rfl,fun model => (holds packet allocated reserved model).symm,
    fun model => (inputs packet allocated reserved model).symm,fun model => (outputs packet allocated reserved model).symm⟩,
    ?_,(named_schema packet allocated reserved).symm,(input_schema packet allocated reserved).symm,rfl,
    (capture packet allocated reserved).symm,?_⟩
  · intro observed
    unfold GeneralNominalLedgerPermutation.Reads
    dsimp only [rebase]
    rw [GeneralNominalMetadataInspection.queries,GeneralNominalMetadataInspection.readsMany]
    simp only [GeneralNominalMetadataInspection.head]
    rfl
  · intro models name origin
    unfold GeneralNominalSharedCaptures.Captured
    rw [inherited_report]
    simp [GeneralNominalReportMetadata.report,GeneralNominalReportMetadata.capture]
    intro _
    constructor
    · rintro ⟨entry,member,name,origin⟩
      exact ⟨⟨entry.name,entry.bounds,entry.origin⟩,⟨entry,member,rfl⟩,name,origin⟩
    · rintro ⟨_,⟨entry,member,rfl⟩,name,origin⟩
      exact ⟨entry,member,name,origin⟩

end Yulang.GeneralNominalPacketMetadata
