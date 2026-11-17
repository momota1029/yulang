import Yulang.GeneralNominalVersionedRevisit231
import Yulang.GeneralNominalVersionedPlans231
set_option backward.isDefEq.respectTransparency false

/-! Exact fixed-observation reconstruction under ordinary extension. Only
ordinary constraints, reservations and ownership are appended; heads, nominal
observations, source IDs, interpretation and actual centers do not change.
This is not transport through Refresh/Reobserve or a successor boundary. -/
namespace Yulang.GeneralNominalVersionedTransport231
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedFrame231
open GeneralNominalVersionedPlans231

variable (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
  (allocated : List GeneralNominalIdentities.Origin)

def extendedPacket (packet : Packet roles) : Packet roles :=
  { packet with context := GeneralDictionaryOrdinaryTransport.extend packet.context reserved atoms allocated }

def extendedPlan (plan : Plan roles) : Plan roles :=
  ⟨extendedPacket reserved atoms allocated plan.packet,plan.input,plan.input_exact⟩

theorem plan_packet (plan : Plan roles) :
    (extendedPlan reserved atoms allocated plan).packet = extendedPacket reserved atoms allocated plan.packet := rfl

theorem plan_input (plan : Plan roles) :
    (extendedPlan reserved atoms allocated plan).input = plan.input := rfl

theorem packet_declaration (packet : Packet roles) :
    (extendedPacket reserved atoms allocated packet).declaration = packet.declaration := rfl

theorem needed_iff (packet : Packet roles) (name : Nat) :
    GeneralNominalSharedCaptures.Needed (extendedPacket reserved atoms allocated packet) name ↔
      GeneralNominalSharedCaptures.Needed packet name := Iff.rfl

theorem packet_bindings (packet : Packet roles) :
    (extendedPacket reserved atoms allocated packet).bindings = packet.bindings := by
  unfold GeneralNominalSaturationState.Packet.bindings extendedPacket
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.bindings_report]

theorem frame_eq (packet : Packet roles) :
    frame (extendedPacket reserved atoms allocated packet) = frame packet := by
  unfold frame
  rw [packet_bindings]
  rfl

theorem capture_eq (packet : Packet roles) :
    capture (extendedPacket reserved atoms allocated packet) = capture packet := by
  unfold capture
  rw [frame_eq]
  rfl

theorem binder_eq (plan : Plan roles) (name : Nat) :
    binder (extendedPlan reserved atoms allocated plan) name = binder plan name := by
  unfold binder extendedPlan
  rw [capture_eq]
  rfl

theorem children_eq (packet : Packet roles) :
    children (extendedPacket reserved atoms allocated packet) = children packet := by
  unfold children
  rw [frame_eq]
  rfl

theorem clauseChild_eq (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    clauseChild (extendedPacket reserved atoms allocated packet) clause valid = clauseChild packet clause valid := by
  unfold clauseChild
  rw [frame_eq,capture_eq]
  rfl

theorem emittedCenter_eq (plan : Plan roles) (clause position : Nat) (pattern) :
    emittedCenter (extendedPlan reserved atoms allocated plan) clause position pattern =
      emittedCenter plan clause position pattern := by
  unfold emittedCenter
  cases GeneralDeclarationPatterns.normalize pattern <;> first | exact binder_eq _ _ _ _ _ | rfl

theorem childSite_eq (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    childSite (extendedPlan reserved atoms allocated plan) clause valid = childSite plan clause valid := by
  unfold childSite
  simp only [plan_packet,emittedCenter_eq]
  congr 1
  exact clauseChild_eq reserved atoms allocated plan.packet clause valid

theorem emittedRequests_eq (packet : Packet roles) :
    emittedRequests (extendedPacket reserved atoms allocated packet) = emittedRequests packet := by
  unfold emittedRequests
  rw [capture_eq,frame_eq]
  rfl

theorem emittedSchema_eq (plan : Plan roles) :
    emittedSchema (extendedPlan reserved atoms allocated plan) = emittedSchema plan := by
  unfold emittedSchema extendedPlan
  rw [emittedRequests_eq]
  rfl

theorem variables_eq (plan : Plan roles) (model) :
    variables (extendedPlan reserved atoms allocated plan) model = variables plan model := by
  funext mode name
  unfold variables
  rw [binder_eq]
  simp only [plan_packet,capture_eq,packet_declaration]

theorem childRequests_eq (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    childRequests (extendedPlan reserved atoms allocated plan) clause valid = childRequests plan clause valid := by
  unfold childRequests childSite
  simp only [emittedCenter_eq]

theorem childSchema_eq (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    childSchema (extendedPlan reserved atoms allocated plan) clause valid = childSchema plan clause valid := by
  unfold childSchema
  rw [childRequests_eq]
  rfl

theorem headSchema_eq (plan : Plan roles) :
    (extendedPlan reserved atoms allocated plan).headSchema = plan.headSchema := rfl

theorem schemaHolds_iff (plan : Plan roles) (schema) (model) :
    SchemaHolds (extendedPlan reserved atoms allocated plan) schema model ↔ SchemaHolds plan schema model := by
  unfold SchemaHolds
  simp only [binder_eq,plan_packet,capture_eq,packet_declaration]

theorem ordinary_iff (packet : Packet roles) (model) :
    Ordinary (extendedPacket reserved atoms allocated packet) model ↔ Ordinary packet model := by
  unfold Ordinary
  rw [packet_bindings]
  change (_ ∧ _ ∧ PresenceNormalForm.All _ model
    (GeneralNominalRecursiveInspection.selfChecks _
      (GeneralNominalRecursiveCandidates.report (GeneralDictionaryOrdinaryTransport.extend packet.context reserved atoms allocated) packet.declaration packet.bounds))) ↔ _
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.selfChecks_report]
  rfl

theorem projection_iff (packet : Packet roles) (model) :
    GeneralNominalRecursiveInspection.ProjectionModels (extendedPacket reserved atoms allocated packet).context.state
      (GeneralNominalPacketSupport.report (extendedPacket reserved atoms allocated packet)) model ↔
    GeneralNominalRecursiveInspection.ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) model := by
  unfold GeneralNominalPacketSupport.report extendedPacket
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.projection_report]

theorem inputs_iff (plan : Plan roles) (model) :
    Inputs (extendedPlan reserved atoms allocated plan) model ↔ Inputs plan model := by
  unfold Inputs
  simp only [plan_packet,plan_input,packet_declaration,needed_iff,ordinary_iff,projection_iff,capture_eq,binder_eq,
    headSchema_eq,schemaHolds_iff,emittedSchema_eq,variables_eq,childSite_eq,childSchema_eq]

theorem outputs_iff (plan : Plan roles) (model) :
    Outputs (extendedPlan reserved atoms allocated plan) model ↔ Outputs plan model := by
  unfold Outputs
  rw [emittedSchema_eq,variables_eq]

/-- Exact total-packet reconstruction, retaining every Inputs/Outputs condition.
Only the newly appended ordinary atoms are additional semantic obligations. -/
theorem holds_iff (plan : Plan roles) (model) :
    Holds (extendedPlan reserved atoms allocated plan) model ↔
      Holds plan model ∧ PresenceNormalForm.All CommonNominalFullCarrier.model model atoms := by
  unfold Holds
  rw [inputs_iff,outputs_iff]
  change (GeneralNominalState.Models (GeneralDictionaryOrdinaryTransport.extendState plan.packet.context.state reserved atoms allocated) model ∧ _) ↔ _
  rw [GeneralDictionaryOrdinaryTransport.models_extended]
  constructor
  · rintro ⟨⟨old,added⟩,rest⟩
    exact ⟨⟨old,rest⟩,added⟩
  · rintro ⟨⟨old,rest⟩,added⟩
    exact ⟨⟨old,added⟩,rest⟩

end Yulang.GeneralNominalVersionedTransport231
