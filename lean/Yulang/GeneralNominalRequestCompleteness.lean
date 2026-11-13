import Yulang.GeneralNominalHeadMatchMass

/-! The actual candidate preparation certificate supplies supported child
queries. Ordinary model satisfaction alone does not carry this fact. -/
namespace Yulang.GeneralNominalRequestCompleteness
open GeneralNominalInspection (Query)
open GeneralNominalMaterialization GeneralNominalSaturationState GeneralDeclarations
open GeneralDeclarationPatterns GeneralNominalHeadMatchMass

mutual
  theorem schema_complete (query : Query) (origin : GeneralNominalRecursiveInspection.Origin) (mode : Mode)
      (known : (schema query origin mode).unknown = false) : Complete query := by
    cases query with
    | variables | scalar => simp only [Complete]
    | deferred => simp only [schema] at known; cases known
    | node shape children =>
      simp only [schema] at known
      simp only [Complete]
      exact schemas_complete children _ mode 0 known
    | nominal name children =>
      simp only [schema] at known
      simp only [Complete]
      exact schemas_complete children _ .actual 0 known
    termination_by sizeOf query
  theorem schemas_complete (queries : List Query) (origins : Nat → GeneralNominalRecursiveInspection.Origin)
      (mode : Mode) (offset : Nat) (known : (schemas queries origins mode offset).unknown = false) :
      ∀ query ∈ queries, Complete query := by
    cases queries with
    | nil => intro query member; cases member
    | cons head tail =>
      have parts : (schema head (origins offset) mode).unknown = false ∧
          (schemas tail origins mode (offset+1)).unknown = false := by
        simpa only [schemas,Schema.append,Bool.or_eq_false_iff] using known
      intro query member
      rcases List.mem_cons.mp member with same | member
      · exact same.symm ▸ schema_complete head _ mode parts.1
      · exact schemas_complete tail origins mode (offset+1) parts.2 query member
    termination_by sizeOf queries
end

theorem generated_complete (state : GeneralNominalState.State) (interpretation : GeneralNominalInspection.Interpretation)
    (requests : List Request) (known : (generated state interpretation requests).unknown = false)
    (request : Request) (member : request ∈ requests) :
    Complete (GeneralNominalInspection.translate state.constructors interpretation (normalize request.pattern)) := by
  induction requests with
  | nil => cases member
  | cons head tail ih =>
    have parts : (schema (GeneralNominalInspection.translate state.constructors interpretation (normalize head.pattern))
        (.source head.target) head.mode).unknown = false ∧ (generated state interpretation tail).unknown = false := by
      simpa only [generated,List.map_cons,List.foldr_cons,Schema.append,Bool.or_eq_false_iff] using known
    rcases List.mem_cons.mp member with rfl | member
    · exact schema_complete _ _ _ parts.1
    · exact ih parts.2 member

theorem input_request_member (packet : Packet roles) (request : Request)
    (member : request ∈ GeneralNominalPacketSupport.inputRequests packet) :
    request ∈ requests packet.context.state packet.registry packet.site.occurrence packet.declaration packet.checked packet.bindings := by
  obtain ⟨emission,emitted,present⟩ := List.mem_flatMap.mp member
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨emission,emitted,List.mem_append_left _ present⟩

theorem request_ready (packet : Packet roles)
    (prepared : GeneralNominalRecursiveCandidates.Prepared packet.registry packet.context packet.site.occurrence packet.declaration packet.checked)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds) :
    GeneralNominalRecursiveCandidates.RequestReady packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds := by
  obtain ⟨_,_,_,bounds,found,_,ready,_⟩ := prepared
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  exact ready

theorem input_complete (state : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (compound : ∀ name, normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) ≠ .var name) :
    Complete (GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (normalize (GeneralNominalCompoundEmission.lowerRequest packet clause signature index).pattern)) := by
  obtain ⟨_,_,_,_,_,located,prepared,_,_,_,_,_⟩ := enabled.1
  have ready := request_ready packet prepared located
  exact generated_complete packet.context.state packet.context.interpretation _ ready.2 _
    (input_request_member packet _ (GeneralNominalCompoundEmission.emitted_requests packet clause present signature index compound).1)

end Yulang.GeneralNominalRequestCompleteness
