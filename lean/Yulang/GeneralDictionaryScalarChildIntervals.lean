import Yulang.GeneralDictionaryGeneratedIntervals
import Yulang.GeneralDictionaryRecordedRequestModels

/-! Actual compound scalar where-input endpoints, derived from both emitted
materialization requests. The endpoints are allocated independently; order is
not an input hypothesis. Arbitrary nominal/structural inputs are not covered. -/
namespace Yulang.GeneralDictionaryScalarChildIntervals
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalMaterialization
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

theorem scalar_request (packet : Packet roles) (request : Request)
    (present : request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings)
    (base : Inference.Base)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = .scalar base)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    Equivalent (model request.target).1 (.base base) := by
  have test : (Origin.source request.target,Test.scalar base) ∈
      (generated packet.context.state packet.context.interpretation [request]).tests := by
    simp [generated,translated,schema,Schema.append]
  have included := GeneralDictionaryRecordedRequestModels.subset_tests packet.context.state
    packet.context.interpretation [request] _ (by intro r hr; simpa using (List.mem_singleton.mp hr ▸ present)) _ test
  exact (valid.2.2.1 _ included).2 _ (.source request.target)

theorem emission_request (packet : Packet roles) (clause : Clause)
    (member : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (request : Request)
    (present : request ∈ emissionRequests (emit packet.site.occurrence.identity packet.declaration clause signature
      (GeneralNominalPacketSupport.capture packet)
      (GeneralNominalAllocation.allocation packet.context.state packet.registry packet.site.occurrence.identity packet.declaration.id clause))) :
    request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨_,?_,present⟩
  apply (GeneralCanonicalChildOrder.canonicalEmit_perm ..).mem_iff.mp
  apply List.mem_map.mpr
  exact ⟨⟨clause,member⟩,by simp,rfl⟩

theorem clause_scalar_order (packet : Packet roles) (clause : Clause)
    (member : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) (base : Inference.Base)
    (key : Nat)
    (shape : GeneralDeclarationPatterns.normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .app key [])
    (primitive : packet.context.interpretation.primitives key = some (.scalar base))
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    let child := GeneralNominalFeedbackSites.clauseChild packet clause signature
    Subtype (model (child.demand.arguments index).1).1 (model (child.demand.arguments index).2).1 := by
  have indexValid : index.val < clause.arguments.length := by rw [signature.1]; exact index.isLt
  let emission := emit packet.site.occurrence.identity packet.declaration clause signature
    (GeneralNominalPacketSupport.capture packet)
    (GeneralNominalAllocation.allocation packet.context.state packet.registry packet.site.occurrence.identity packet.declaration.id clause)
  let input : InputRequest := ⟨index.val,clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt),emission.demand.arguments index⟩
  have inputMember : input ∈ emission.inputs := List.mem_ofFn.mpr ⟨index,rfl⟩
  have translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize input.pattern) = .scalar base := by
    change GeneralNominalInspection.translate _ _ (GeneralDeclarationPatterns.normalize clause.arguments[index.val]) = _
    rw [shape]
    simp [GeneralNominalInspection.translate,primitive]
  have notvar : ∀ name, GeneralDeclarationPatterns.normalize input.pattern ≠ .var name := by
    intro name eq
    have t := translated
    change GeneralNominalInspection.translate _ _ (GeneralDeclarationPatterns.normalize input.pattern) = _ at t
    rw [eq] at t
    simp [GeneralNominalInspection.translate] at t
  have reqs : inputRequests input = [⟨GeneralDeclarationPatterns.normalize input.pattern,input.endpoints.1,.lower⟩,
      ⟨GeneralDeclarationPatterns.normalize input.pattern,input.endpoints.2,.upper⟩] := by
    unfold inputRequests
    split <;> simp_all
  have requestMember : ∀ request ∈ inputRequests input, request ∈ requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings := by
    intro request hr
    apply emission_request packet clause member signature request
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨input,inputMember,hr⟩)
  have lower := scalar_request packet ⟨GeneralDeclarationPatterns.normalize input.pattern,input.endpoints.1,.lower⟩
    (requestMember _ (by rw [reqs]; simp)) base (by change GeneralNominalInspection.translate _ _ (GeneralDeclarationPatterns.normalize (GeneralDeclarationPatterns.normalize clause.arguments[index.val])) = _; rw [shape]; simp [GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,GeneralNominalInspection.translate,primitive]) model valid
  have upper := scalar_request packet ⟨GeneralDeclarationPatterns.normalize input.pattern,input.endpoints.2,.upper⟩
    (requestMember _ (by rw [reqs]; simp)) base (by change GeneralNominalInspection.translate _ _ (GeneralDeclarationPatterns.normalize (GeneralDeclarationPatterns.normalize clause.arguments[index.val])) = _; rw [shape]; simp [GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,GeneralNominalInspection.translate,primitive]) model valid
  exact subtype_trans lower.1 upper.2

/-- Syntactic restriction for this proof only: actual where inputs are variables
or zero-argument interpreted scalar constructors. No new acceptance rule. -/
def ScalarVariableInputs (packet : Packet roles) : Prop :=
  ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
    ∀ index : Fin (roles clause.role).arity,
      (∃ name, GeneralDeclarationPatterns.normalize
        (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .var name) ∨
      (∃ key base, GeneralDeclarationPatterns.normalize
        (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .app key [] ∧
        packet.context.interpretation.primitives key = some (.scalar base))

theorem variable_inputs_included (packet : Packet roles)
    (shape : GeneralDictionaryCapturedChildIntervals.VariableInputs packet) : ScalarVariableInputs packet := by
  intro clause member signature index
  exact Or.inl (shape clause member signature index)

theorem child_intervals (packet : Packet roles) (shape : ScalarVariableInputs packet)
    (child : Occurrence roles) (member : child ∈ packet.children)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (index : Fin (roles child.demand.role).arity) :
    Subtype (model (child.demand.arguments index).1).1 (model (child.demand.arguments index).2).1 := by
  obtain ⟨clause,present,signature,rfl⟩ := GeneralDictionaryCapturedChildIntervals.child_origin packet child member
  rcases shape clause present signature index with ⟨name,patternEq⟩ | ⟨key,base,patternEq,primitive⟩
  · exact GeneralDictionaryCapturedChildIntervals.clause_input_order packet clause signature index name patternEq
      (GeneralDictionaryCapturedChildIntervals.clause_input_declared packet clause present signature index name patternEq) model valid
  · exact clause_scalar_order packet clause present signature index base key patternEq primitive model valid

/-- Every real journal packet must satisfy the stated syntactic input fragment.
This is weaker than VariableJournal; arbitrary compound constructors remain out of scope. -/
def ScalarVariableJournal (state : GeneralNominalSupport.Tracked roles) : Prop :=
  ∀ packet ∈ state.current.packets, ScalarVariableInputs packet

theorem generated_intervals {registry : Registry} {root child : Occurrence roles}
    {state : GeneralNominalSupport.Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (journal : ScalarVariableJournal state) (reached : Generated state.current root child)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalSaturationState.Models state.current model) (index) :
    Subtype (model (child.demand.arguments index).1).1 (model (child.demand.arguments index).2).1 := by
  rcases GeneralDictionaryGeneratedOrigins.reachable_generated reachable reached with same | ⟨packet,recorded,emitted⟩
  · subst child
    exact GeneralDictionaryReachableRootIntervals.root_intervals registry root state reachable model valid index
  · exact child_intervals packet (journal packet recorded) child emitted model (valid.2.1 packet recorded) index

theorem located_intervals {registry : Registry} {root child : Occurrence roles}
    {state : GeneralNominalSupport.Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (journal : ScalarVariableJournal state) (reached : Generated state.current root child)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (located : GeneralNominalCandidates.arguments state.current.context child = some bounds)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalSaturationState.Models state.current model) :
    ∀ pair ∈ bounds, Subtype (model (state.current.context.state.base.source pair.1)).1
      (model (state.current.context.state.base.source pair.2)).1 := by
  intro pair member
  have same := GeneralDictionaryReachableRootIntervals.locate_sources state.current.context.state.base
    (List.ofFn child.demand.arguments) bounds located
  have present : (state.current.context.state.base.source pair.1,state.current.context.state.base.source pair.2) ∈
      List.ofFn child.demand.arguments := by
    rw [←same]
    exact List.mem_map.mpr ⟨pair,member,rfl⟩
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp present
  have result := generated_intervals reachable journal reached model valid index
  simpa only [equal] using result

end Yulang.GeneralDictionaryScalarChildIntervals
