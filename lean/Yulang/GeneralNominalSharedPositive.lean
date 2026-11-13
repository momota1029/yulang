import Yulang.GeneralNominalSharedSteps
import Yulang.GeneralNominalSupportExamples

/-! Positive certificate constructors: strict retained captures, point uses,
constant outputs, and implementations without generated children. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalSharedPositive
open GeneralNominalSaturationState GeneralNominalRecursiveInspection GeneralNominalSharedCaptures
open GeneralNominalOriginTerms GeneralNominalSupport GeneralDeclarations
open GeneralNominalCommonBridge (Assignment)

theorem leaf_input_schema (packet : Packet roles) (empty : packet.declaration.requirements = []) :
    GeneralNominalPacketSupport.inputSchema packet = {} := by
  let emitted := GeneralCanonicalChildOrder.canonicalEmit packet.site.occurrence.identity packet.declaration
    packet.checked (GeneralNominalPacketSupport.capture packet)
    (GeneralNominalAllocation.allocation packet.context.state packet.registry packet.site.occurrence.identity packet.declaration.id)
  have size := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity packet.declaration
    packet.checked (GeneralNominalPacketSupport.capture packet)
    (GeneralNominalAllocation.allocation packet.context.state packet.registry packet.site.occurrence.identity packet.declaration.id)).length_eq
  rw [GeneralDeclarationDemands.emitAll_length,empty] at size
  have absent : emitted = [] := List.eq_nil_of_length_eq_zero size.symm
  change GeneralNominalMaterialization.generated _ _ (emitted.flatMap _) = _
  rw [absent]
  rfl

theorem leaf_input_coherent (packet : Packet roles) (empty : packet.declaration.requirements = []) :
    InputCoherence packet := empty_input_coherent (by rw [leaf_input_schema packet empty])

theorem single_capture_usable (packet : Packet roles) (name : Nat)
    (bounds : GeneralNominalInspection.Bounds packet.context.state) (origin : Origin)
    (original : (GeneralNominalPacketSupport.report packet).captures = [⟨name,bounds,some origin⟩])
    (inherited : (inheritedReport packet).captures = [⟨name,bounds,some origin⟩])
    (anchor : (origin,bounds) ∈ (GeneralNominalPacketSupport.report packet).anchors) :
    Usable packet name origin := by
  have binding : packet.bindings = [(name,(packet.context.state.base.source bounds.1,packet.context.state.base.source bounds.2))] := by
    change bindings _ (GeneralNominalPacketSupport.report packet) = _
    simp only [bindings,original,List.map_cons,List.map_nil]
  have interval : (GeneralNominalPacketSupport.capture packet).inputs name =
      (packet.context.state.base.source bounds.1,packet.context.state.base.source bounds.2) := by
    unfold GeneralNominalPacketSupport.capture
    rw [binding]
    simp [GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences]
  have seen (model : Assignment) (valid : packet.Holds model) := valid.2.1.1 _ anchor
  refine ⟨⟨⟨⟨name,bounds,some origin⟩,?_,rfl,rfl⟩,?_⟩,?_⟩
  · rw [inherited]; simp
  · intro captured member same
    rw [inherited] at member
    cases List.mem_singleton.mp member
    refine ⟨origin,rfl,?_⟩
    intro model valid
    refine ⟨(seen model valid).1,(seen model valid).1,?_⟩
    intro a b one two
    have member : (⟨name,bounds,some origin⟩ : Capture packet.context.state) ∈
        (GeneralNominalPacketSupport.report packet).captures := by rw [original]; simp
    exact valid.2.1.2.2.2 _ member _ member rfl origin origin rfl rfl a b one two
  · intro model valid
    rw [interval]
    exact seen model valid

theorem constant_certificate (state : Tracked roles) (facts readbacks) (packet : Packet roles)
    (empty : (GeneralNominalPacketSupport.namedSchema packet).variables = [])
    (recipes : GeneralNominalSharedSupport.Recipes packet) :
    Nonempty (GeneralNominalSharedSupport.OutputCertificate state facts readbacks packet) := by
  refine ⟨⟨fun _ => .leaf (.source 0),recipes,?_,?_,?_⟩⟩
  · intro entry member; rw [empty] at member; cases member
  · intro entry member; rw [empty] at member; cases member
  · intro model source delta entry member; rw [empty] at member; cases member

theorem initial_decision (context : GeneralNominalCandidates.Context) (root focus : GeneralSourceDictionaries.Occurrence roles)
    (registry : Registry) (support : List (GeneralSourceDictionaries.Occurrence roles))
    (old : GeneralNominalSupport.DecisionGuard (initial context root) registry focus support) :
    GeneralNominalSharedSupport.DecisionGuard registry (initial context root) focus := by
  have ready (identity) (known : GeneralNominalSupport.ReadyAt (initial context root) support identity) :
      GeneralNominalSharedSupport.ReadyAt (initial context root) identity := by
    obtain ⟨test,observation,head,snapshot,witness,recorded,entailed⟩ := known
    refine ⟨test,observation,head,[],[],.source,snapshot,witness,recorded,?_⟩
    intro model valid
    exact entailed model ⟨valid.1,by intro fact member; cases member⟩
  exact ⟨fun index => ready _ (old.2.1 index),
    fun declaration member role bounds located slot read => ready _ (old.2.2 declaration member role bounds located slot read)⟩

variable {model : Assignment}

theorem binder_readback (valid : GeneralNominalMaterialization.Models state declaration capture report body model)
    (member : entry ∈ body.variables) (output : entry.name ∈ declaration.outputNames)
    (readback : Holds model term (.source (capture.outputs entry.name))) : Holds model term entry.origin :=
  holds_transport (same_symm (output_binder_use valid member output)) readback

end Yulang.GeneralNominalSharedPositive
