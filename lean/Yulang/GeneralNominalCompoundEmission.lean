import Yulang.GeneralNominalCompoundRecovery

/-! Connect compound request targets to the actual clause emitter. The
resulting endpoint equality is consumed by the existing root recovery. -/
namespace Yulang.GeneralNominalCompoundEmission
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralNominalSaturationState GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCompoundReadback GeneralNominalCompoundRecovery GeneralNominalReadbackFunctionality
open GeneralNominalOriginTerms GeneralNominalFeedbackSites GeneralNominalSharedCaptures

def lowerRequest (packet : Packet roles) (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) : Request :=
  ⟨normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)),
    ((clauseChild packet clause signature).demand.arguments index).1,.lower⟩

def upperRequest (packet : Packet roles) (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) : Request :=
  ⟨normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)),
    ((clauseChild packet clause signature).demand.arguments index).2,.upper⟩

theorem emitted_requests (packet : Packet roles) (clause : Clause)
    (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (compound : ∀ binder, normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) ≠ .var binder) :
    lowerRequest packet clause signature index ∈ GeneralNominalPacketSupport.inputRequests packet ∧
    upperRequest packet clause signature index ∈ GeneralNominalPacketSupport.inputRequests packet := by
  let allocation := GeneralNominalAllocation.allocation (roles := roles) packet.context.state packet.registry
    packet.site.occurrence.identity packet.declaration.id
  let emission := emit packet.site.occurrence.identity packet.declaration clause signature
    (GeneralNominalPacketSupport.capture packet) (allocation clause)
  have emitted : emission ∈ GeneralCanonicalChildOrder.canonicalEmit packet.site.occurrence.identity
      packet.declaration packet.checked (GeneralNominalPacketSupport.capture packet) allocation := by
    apply (GeneralCanonicalChildOrder.canonicalEmit_perm ..).mem_iff.mp
    exact List.mem_map.mpr ⟨⟨clause,present⟩,List.mem_attach ..,rfl⟩
  let input : InputRequest := ⟨index.val,clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt),
    emission.demand.arguments index⟩
  have inputMem : input ∈ emission.inputs := List.mem_ofFn.mpr ⟨index,rfl⟩
  have requested : lowerRequest packet clause signature index ∈ GeneralNominalMaterialization.inputRequests input ∧
      upperRequest packet clause signature index ∈ GeneralNominalMaterialization.inputRequests input := by
    unfold GeneralNominalMaterialization.inputRequests
    cases normalized : normalize input.pattern with
    | var binder => exact False.elim (compound binder normalized)
    | app key arguments | record label payload tail | variant tag payload | join first last =>
      constructor
      · apply List.mem_cons.mpr; left
        unfold lowerRequest
        rw [show normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = _ from normalized]
        rfl
      · apply List.mem_cons.mpr; right
        apply List.mem_singleton.mpr
        unfold upperRequest
        rw [show normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = _ from normalized]
        rfl
  exact ⟨List.mem_flatMap.mpr ⟨emission,emitted,List.mem_flatMap.mpr ⟨input,inputMem,requested.1⟩⟩,
    List.mem_flatMap.mpr ⟨emission,emitted,List.mem_flatMap.mpr ⟨input,inputMem,requested.2⟩⟩⟩

theorem child_endpoint_equal (state : State roles) (packet : Packet roles) (stored : packet ∈ state.packets)
    (coherence : InputCoherence packet) (clause : Clause) (present : clause ∈ packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (normalize (lowerRequest packet clause signature index).pattern) = quote (.node (.nominal name count) children))
    (canonical : Canonical (.node (.nominal name count) children)) :
    EndpointEqual state ((clauseChild packet clause signature).demand.arguments index) := by
  have compound : ∀ binder, normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) ≠ .var binder := by
    intro binder equal
    unfold lowerRequest at translated
    rw [equal] at translated
    simp only [normalize,GeneralNominalInspection.translate,quote] at translated
    cases translated
  have requests := emitted_requests packet clause present signature index compound
  exact endpoint_equal state packet stored coherence _ _ requests.1 requests.2 translated translated canonical

theorem historical_child_endpoint_equal {roles : Roles.RoleDecls}
    {root : GeneralSourceDictionaries.Occurrence roles} {state : GeneralNominalSupport.Tracked roles}
    (steps : B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (packet : Packet roles) (stored : packet ∈ state.current.packets)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (normalize (lowerRequest packet clause signature index).pattern) = quote (.node (.nominal name count) children))
    (canonical : Canonical (.node (.nominal name count) children)) :
    EndpointEqual state.current ((clauseChild packet clause signature).demand.arguments index) :=
  child_endpoint_equal state.current packet stored (trace_coherence steps packet stored)
    clause present signature index translated canonical

theorem historical_child_root_recovered {roles : Roles.RoleDecls}
    {root : GeneralSourceDictionaries.Occurrence roles} {state : GeneralNominalSupport.Tracked roles}
    (steps : B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (packet : Packet roles) (stored : packet ∈ state.current.packets)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (normalize (lowerRequest packet clause signature index).pattern) = quote (.node (.nominal name count) children))
    (canonical : Canonical (.node (.nominal name count) children))
    (missing : (GeneralNominalSharedEmission.childSite packet (clauseChild packet clause signature)).inputs[index.val]? = some none) :
    (recover state.current (GeneralNominalSharedEmission.childSite packet (clauseChild packet clause signature))).inputs[index.val]? =
      some (some (.source ((clauseChild packet clause signature).demand.arguments index).1)) :=
  root_recovered state.current (GeneralNominalSharedEmission.childSite packet (clauseChild packet clause signature)) index missing
    (historical_child_endpoint_equal steps packet stored clause present signature index translated canonical)

end Yulang.GeneralNominalCompoundEmission
