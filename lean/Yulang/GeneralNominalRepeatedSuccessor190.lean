import Yulang.GeneralNominalRepeatedLocal190

set_option backward.isDefEq.respectTransparency false
/-! Evidence at the actual installed current context, retaining its model. -/
namespace Yulang.GeneralNominalRepeatedSuccessor190
open GeneralNominalRepeatedFixture190
open GeneralNominalRepeatedLocal190
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel

abbrev currentPacket : GeneralNominalSaturationState.Packet roles :=
  { packet with context := packet.privateContext }

open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

theorem current_query : GeneralNominalInspection.queries currentPacket.context.state
    currentPacket.context.interpretation declaration = [.variables [0],.variables [0]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate]

theorem current_report : report currentPacket.context declaration [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))] =
    { captures := [⟨0,((1 : Fin 3),(1 : Fin 3)),none⟩,⟨0,((1 : Fin 3),(1 : Fin 3)),none⟩], checked := [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))] } := by
  unfold report
  rw [current_query]
  simp [inspectMany,inspect,Report.append]

theorem current_ordinary (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalPacketSupport.Ordinary currentPacket model ↔
      GeneralNominalPacketSupport.Ordinary packet model := by
  simp only [GeneralNominalPacketSupport.Ordinary,GeneralNominalSaturationState.Packet.bindings,
    GeneralNominalPacketSupport.report,report,GeneralNominalInspection.queries,
    GeneralDeclarations.Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,List.map_cons,List.map_nil,
    GeneralNominalInspection.translate,inspectMany,inspect,Report.append]
  rfl

theorem current_bindings : currentPacket.bindings = packet.bindings := by
  simp only [GeneralNominalSaturationState.Packet.bindings,report,GeneralNominalInspection.queries,
    GeneralDeclarations.Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,List.map_cons,List.map_nil,
    GeneralNominalInspection.translate,inspectMany,inspect,Report.append]
  rfl

theorem current_capture : GeneralNominalPacketSupport.capture currentPacket = GeneralNominalPacketSupport.capture packet := by
  unfold GeneralNominalPacketSupport.capture
  rw [current_bindings]
  rfl

theorem current_schema : GeneralNominalPacketSupport.namedSchema currentPacket =
    GeneralNominalPacketSupport.namedSchema packet := by
  unfold GeneralNominalPacketSupport.namedSchema generated
  change GeneralNominalMaterialization.generated _ _ (GeneralNominalMaterialization.requests _ _ _ _ _ currentPacket.bindings) = _
  rw [current_bindings]
  rfl

theorem current_branch (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    currentPacket.Holds model := by
  refine ⟨(GeneralNominalPacketSupport.private_exact currentPacket model).mpr ⟨valid.1,?_⟩,?_⟩
  · exact (current_ordinary model).mpr ((GeneralNominalPacketSupport.private_exact packet model).mp valid.1).2
  · have rest := valid.2
    change ProjectionModels _ _ model ∧ GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema packet) model at rest
    change ProjectionModels _ _ model ∧ GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema currentPacket) model
    change ProjectionModels _ _ model ∧ GeneralNominalMaterialization.Models _ _ (GeneralNominalPacketSupport.capture currentPacket) _ _ model
    rw [current_schema,current_capture]
    simpa [ProjectionModels,GeneralNominalMaterialization.Models,
      report,GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,List.map_cons,List.map_nil,
      GeneralNominalInspection.translate,inspectMany,inspect,Report.append,
      Fits,GeneralNominalPacketSupport.capture,GeneralNominalSaturationState.Packet.bindings,bindings] using rest

theorem current_instance (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    GeneralDictionaryRecursiveEvidence.Instance registry packet.privateContext model root 3 [] := by
  refine ⟨declaration,by simp,declaration_checked,rfl,rfl,
    [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))],?_,?_,?_,?_,?_,current_branch model valid⟩
  · exact frame.located
  · rw [current_report]
    exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      cases List.mem_singleton.mp member
      exact ⟨⟨0,0,.var 0⟩,by simp,rfl⟩
    · change (GeneralNominalPacketSupport.namedSchema currentPacket).unknown = false
      rw [current_schema]
      exact (GeneralNominalInitialNamedEvidence189.initial_request_ready initial_source plan frame rfl effects_ready).2
  · simp only [GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children]
    have empty (capture : GeneralDeclarationDemands.Capture)
        (allocate : (clause : GeneralDeclarations.Clause) → GeneralDeclarationDemands.Allocation roles clause) :
        GeneralCanonicalChildOrder.canonicalEmit 100 declaration declaration_checked capture allocate = [] := by
      apply List.Perm.eq_nil
      exact (GeneralCanonicalChildOrder.canonicalEmit_perm ..).symm.trans
        (by simp [GeneralDeclarationDemands.emitAll,declaration])
    rw [empty]
    rfl
  · exact source.metadata

theorem installed_evidence {support : List (GeneralSourceDictionaries.Occurrence roles)}
    (enabled : Installable registry start plan support)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models (install start plan support enabled) model) :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry
      (install start plan support enabled) model root (.node 3 []) := by
  have branch := ((install_models enabled model).mp valid).2.1
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry packet.privateContext model root 3 [] []
    (current_instance model branch.1) .nil

theorem successor_evidence : ∃ after,
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Step registry root start after ∧
    (∃ model, Models after model) ∧
    ∀ model, Models after model →
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry after model root (.node 3 []) := by
  obtain ⟨support,enabled⟩ := installable
  refine ⟨install start plan support enabled,?_,installed_inhabited enabled,installed_evidence enabled⟩
  exact ⟨root,GeneralNominalSaturationState.Generated.root,.install plan support enabled not_committed⟩

end Yulang.GeneralNominalRepeatedSuccessor190
