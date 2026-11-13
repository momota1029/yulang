import Yulang.GeneralNominalReadbackFunctionality
import Yulang.GeneralNominalHoleReadback
import Yulang.GeneralNominalActualTraceSupport

/-! Nominal compound requests recover a shared actual root from their recorded
input schemas. Equality follows from shared captures, never interval overlap. -/
namespace Yulang.GeneralNominalCompoundRecovery
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalMaterialization
open GeneralNominalSharedCaptures GeneralNominalSaturationState GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalFeedbackSites
open GeneralNominalHoleReadback

theorem canonical_bind (term : Expr α) (canonical : Canonical term) (substitution : α → Expr β)
    (leaves : ∀ name, Canonical (substitution name)) : Canonical (term.bind substitution) := by
  induction term with
  | leaf name => exact leaves name
  | node test children ih => exact ⟨canonical.1,fun index => ih index (canonical.2 index)⟩

theorem requests_equal (packet : Packet roles) (coherence : InputCoherence packet)
    (first last : Request)
    (firstMem : first ∈ GeneralNominalPacketSupport.inputRequests packet)
    (lastMem : last ∈ GeneralNominalPacketSupport.inputRequests packet)
    (firstQuery : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize first.pattern) = quote (.node (.nominal name count) children))
    (lastQuery : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize last.pattern) = quote (.node (.nominal name count) children))
    (canonical : Canonical (.node (.nominal name count) children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    CommonNominalFullCarrier.Equivalent (model first.target).1 (model last.target).1 :=
  source_readbacks_equal _ (canonical_bind _ canonical _ (by intro binder; trivial))
    (input_request_readback packet coherence first firstMem firstQuery model valid)
    (input_request_readback packet coherence last lastMem lastQuery model valid)

theorem endpoint_equal (state : State roles) (packet : Packet roles) (stored : packet ∈ state.packets)
    (coherence : InputCoherence packet) (first last : Request)
    (firstMem : first ∈ GeneralNominalPacketSupport.inputRequests packet)
    (lastMem : last ∈ GeneralNominalPacketSupport.inputRequests packet)
    (firstQuery : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize first.pattern) = quote (.node (.nominal name count) children))
    (lastQuery : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize last.pattern) = quote (.node (.nominal name count) children))
    (canonical : Canonical (.node (.nominal name count) children)) :
    EndpointEqual state (first.target,last.target) :=
  fun model valid => requests_equal packet coherence first last firstMem lastMem firstQuery lastQuery
    canonical model (valid.2.1 packet stored)

theorem root_recovered (state : State roles) (site : GeneralNominalDemandMerging.Site roles)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (missing : site.inputs[index.val]? = some none)
    (equal : EndpointEqual state (site.occurrence.demand.arguments index)) :
    (recover state site).inputs[index.val]? =
      some (some (.source (site.occurrence.demand.arguments index).1)) := by
  classical
  have bounds : index.val < site.inputs.length := by rw [site.arity]; exact index.isLt
  have missing' : site.inputs[index.val]'bounds = none := by
    exact Option.some.inj ((List.getElem?_eq_getElem bounds).symm.trans missing)
  simp [recover,recoverOrigin,missing',equal,index.isLt]

theorem input_over_basis (packet : Packet roles) (coherence : InputCoherence packet)
    (request : Request) (requested : request ∈ GeneralNominalPacketSupport.inputRequests packet)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = quote (.node (.nominal name count) children))
    (basis : List Origin) (substitution : Origin → Expr Origin)
    (represented : ∀ binder ∈ (Expr.node (.nominal name count) children).leaves,
      Over packet.Holds basis (representative packet binder) (substitution (representative packet binder))) :
    Over packet.Holds basis (.source request.target)
      (((Expr.node (.nominal name count) children).bind
        (fun binder => .leaf (representative packet binder))).bind substitution) := by
  let middle := (Expr.node (.nominal name count) children).leaves.map (representative packet)
  have initial : Over packet.Holds middle (.source request.target)
      ((Expr.node (.nominal name count) children).bind (fun binder => .leaf (representative packet binder))) := by
    constructor
    · exact fun model valid => input_request_readback packet coherence request requested translated model valid
    · intro leaf member
      obtain ⟨binder,present,found⟩ := (leaves_bind _ _ leaf).mp member
      have equal : leaf = representative packet binder := List.mem_singleton.mp found
      exact List.mem_map.mpr ⟨binder,present,equal.symm⟩
  apply compose initial substitution
  intro origin member
  obtain ⟨binder,present,rfl⟩ := List.mem_map.mp member
  exact represented binder present

theorem trace_coherence
    (steps : B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (GeneralNominalSupport.initial context root) state) :
    ∀ packet ∈ state.current.packets, InputCoherence packet := by
  induction steps with
  | refl => intro packet member; cases member
  | @tail before after steps step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue | refresh | equate | reobserve => exact ih
    | merge => exact ih
    | install packet support enabled novel guard =>
      intro current member
      rcases List.mem_cons.mp member with rfl | old
      · exact guard.1.2.2.2
      · exact ih current old

theorem historical_input_readback {roles : Roles.RoleDecls} {root : GeneralSourceDictionaries.Occurrence roles}
    {state : GeneralNominalSupport.Tracked roles}
    (steps : B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (packet : Packet roles) (stored : packet ∈ state.current.packets)
    (request : Request) (requested : request ∈ GeneralNominalPacketSupport.inputRequests packet)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = quote (.node (.nominal name count) children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Holds model ((Expr.node (.nominal name count) children).bind
      (fun binder => .leaf (representative packet binder))) (.source request.target) :=
  input_request_readback packet (trace_coherence steps packet stored) request requested translated model
    (valid.2.1 packet stored)

end Yulang.GeneralNominalCompoundRecovery
