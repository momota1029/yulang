import Yulang.GeneralNominalReobservationSteps

/-! Separate newly installed input facts from named-output materialization.
Neither component contains the packet's cached raw observation context. The
full named schema is retained, including cross-equations with input uses. -/
namespace Yulang.GeneralNominalPacketSupport

open GeneralNominalSaturationState GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization

abbrev capture (packet : Packet roles) := GeneralNominalAllocation.capture packet.context.state
  packet.registry packet.site.occurrence.identity packet.declaration.id packet.bindings

abbrev report (packet : Packet roles) :=
  GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds

def inputRequests (packet : Packet roles) : List Request :=
  (GeneralCanonicalChildOrder.canonicalEmit packet.site.occurrence.identity packet.declaration packet.checked
    (capture packet) (GeneralNominalAllocation.allocation packet.context.state packet.registry
      packet.site.occurrence.identity packet.declaration.id)).flatMap fun emission =>
        emission.inputs.flatMap GeneralNominalMaterialization.inputRequests

def inputSchema (packet : Packet roles) : Schema :=
  generated packet.context.state packet.context.interpretation (inputRequests packet)

def namedSchema (packet : Packet roles) : Schema :=
  GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
    packet.declaration packet.checked packet.bounds

def Ordinary (packet : Packet roles) (model : Assignment) : Prop :=
  GeneralNominalAllocation.Compatible packet.bindings model ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges packet.context.state packet.registry packet.site.occurrence.identity
        packet.declaration packet.bindings) ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks packet.context.state (report packet))

def Inputs (packet : Packet roles) (model : Assignment) : Prop :=
  Ordinary packet model ∧ ProjectionModels packet.context.state (report packet) model ∧
    GeneralNominalMaterialization.Models packet.context.state packet.declaration (capture packet)
      (report packet) (inputSchema packet) model

def Outputs (packet : Packet roles) (model : Assignment) : Prop :=
  GeneralNominalMaterialization.Models packet.context.state packet.declaration (capture packet)
    (report packet) (namedSchema packet) model

theorem private_exact (packet : Packet roles) (model : Assignment) :
    GeneralNominalState.Models packet.privateContext.state model ↔
      GeneralNominalState.Models packet.context.state model ∧ Ordinary packet model := by
  change GeneralNominalState.Models (GeneralNominalRecursiveCandidates.privateState _ _ _ _ _) model ↔ _
  unfold GeneralNominalRecursiveCandidates.privateState
  rw [GeneralNominalState.extend_models,GeneralNominalAllocation.propagate_models]
  change ((GeneralNominalState.Models packet.context.state model ∧ _ ∧ _) ∧ _) ↔ _
  simp only [Ordinary,and_assoc,Packet.bindings,report]

private theorem schema_sub (state : GeneralNominalState.State) (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : Report state) (small large : Schema)
    (variables : ∀ entry ∈ small.variables, entry ∈ large.variables)
    (tests : ∀ test ∈ small.tests, test ∈ large.tests) (model : Assignment)
    (valid : GeneralNominalMaterialization.Models state declaration capture report large model) :
    GeneralNominalMaterialization.Models state declaration capture report small model := by
  exact ⟨fun test member => valid.1 test (tests test member),
    fun entry member => valid.2.1 entry (variables entry member),
    fun first one last two => valid.2.2.1 first (variables first one) last (variables last two),
    fun entry member => valid.2.2.2 entry (variables entry member)⟩

private theorem generated_members (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) :
    (generated state interpretation requests).variables = requests.flatMap (fun request =>
      (schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (.source request.target) request.mode).variables) ∧
    (generated state interpretation requests).tests = requests.flatMap (fun request =>
      (schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (.source request.target) request.mode).tests) := by
  induction requests with
  | nil => exact ⟨rfl,rfl⟩
  | cons head tail ih =>
    simpa only [generated,List.map_cons,List.foldr_cons,Schema.append,List.flatMap_cons] using
      And.intro (congrArg (fun rest => (schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize head.pattern)) (.source head.target) head.mode).variables ++ rest) ih.1)
        (congrArg (fun rest => (schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize head.pattern)) (.source head.target) head.mode).tests ++ rest) ih.2)

private theorem input_request_member (packet : Packet roles) (request : Request)
    (member : request ∈ inputRequests packet) : request ∈ requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings := by
  obtain ⟨emission,emitted,member⟩ := List.mem_flatMap.mp member
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨emission,emitted,List.mem_append_left _ member⟩

theorem outputs_inputs (packet : Packet roles) (model : Assignment) (valid : Outputs packet model) :
    GeneralNominalMaterialization.Models packet.context.state packet.declaration (capture packet)
      (report packet) (inputSchema packet) model := by
  apply schema_sub _ _ _ _ _ _ ?_ ?_ model valid
  · intro entry member
    unfold inputSchema at member
    rw [(generated_members ..).1] at member
    change entry ∈ (generated _ _ _).variables
    rw [(generated_members ..).1]
    obtain ⟨request,present,member⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr ⟨request,input_request_member packet request present,member⟩
  · intro test member
    unfold inputSchema at member
    rw [(generated_members ..).2] at member
    change test ∈ (generated _ _ _).tests
    rw [(generated_members ..).2]
    obtain ⟨request,present,member⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr ⟨request,input_request_member packet request present,member⟩

theorem packet_exact (packet : Packet roles) (model : Assignment) : packet.Holds model ↔
    GeneralNominalState.Models packet.context.state model ∧ Inputs packet model ∧ Outputs packet model := by
  change (GeneralNominalState.Models packet.privateContext.state model ∧ _ ∧ _) ↔ _
  rw [private_exact]
  constructor
  · rintro ⟨⟨original,ordinary⟩,projections,outputs⟩
    exact ⟨original,⟨ordinary,projections,outputs_inputs packet model outputs⟩,outputs⟩
  · rintro ⟨original,⟨ordinary,projections,_⟩,outputs⟩
    exact ⟨⟨original,ordinary⟩,projections,outputs⟩

end Yulang.GeneralNominalPacketSupport
