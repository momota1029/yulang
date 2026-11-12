import Yulang.GeneralNominalDownstreamSteps
import Yulang.GeneralNominalSupportSiblings

/-! The concrete Wrap child and a cut certificate for the first downstream
expansion in the P/Container/Wrap schedule. The certificate separates the
semantic cut from the missing complete P,C,W transition construction. No
reachability of a state satisfying that certificate is asserted here. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalDownstreamSiblingFixture

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings
open GeneralNominalDownstreamSupport
open GeneralDeclarationExamples (roles wrap wrap_checked containerChild)
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open CommonNominalFullCarrier

local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

abbrev wrapPacket : Packet roles :=
  ⟨reg,ctx,GeneralNominalDemandMerging.pointSite kidW,wrap,wrap_checked,[(1,1)]⟩

abbrev wrapSignature : containerChild.Signature roles :=
  wrap_checked.signature.2.2.2 containerChild (by simp [wrap])

abbrev wrapChild : Occurrence roles :=
  GeneralNominalFeedbackSites.clauseChild wrapPacket containerChild wrapSignature

abbrev wrapOutput : Nat := GeneralNominalAllocation.source src reg kidW.identity
  (GeneralNominalAllocation.origin kidW.identity wrap.id 2 1 0)

theorem wrap_report : GeneralNominalRecursiveCandidates.report ctx wrap [(1,1)] =
    captured src 1 0 0 (2,2) := by
  apply report_exact ctx wrap 1 (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 (2,2) rfl
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source,GeneralNominalOutputGrowthModels.descriptor]

theorem wrap_bindings : wrapPacket.bindings = [(0,(2,2))] := by
  unfold Packet.bindings
  rw [wrap_report]
  rfl

theorem wrap_child_input (index : Fin (roles wrapChild.demand.role).arity) :
    wrapChild.demand.arguments index = (2,2) := by
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  simp [wrapChild,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
    wrap_bindings,GeneralNominalAllocation.occurrences,zero,containerChild,GeneralDeclarationPatterns.normalize]

theorem wrap_child_output : wrapChild.demand.outputs = [⟨1,wrapOutput⟩] := by
  simp [wrapChild,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.outputTarget,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
    wrapOutput,Declaration.outputNames,GeneralDeclarationPatterns.normalize]
  rfl

theorem wrap_children : wrapPacket.children = [wrapChild] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralNominalFeedbackSites.clauseChild,
    GeneralNominalFeedbackSites.frame,wrapPacket,GeneralDictionaryEmissionPlans.occurrence,wrapChild]

/-- Prefix facts needed for the cut argument. In the proposed execution the
cut keeps C0's item equation and removes W0's provisional out equation. The
journal head certificate is required before, and independently of, refresh. -/
structure PrefixCertificate (state : Tracked roles) : Prop where
  source : state.source = ctx
  wrap_open : ¬ Discharged state.current kidW
  child_open : ¬ Discharged state.current wrapChild
  generated : Waiting state.current kidW wrapChild
  head : Available state 2 (.nominal 0 1)
  cut : ∀ fact ∈ state.facts, kidW ∉ fact.dependencies →
    fact.Holds (GeneralNominalOutputGrowth.finiteModel 1)

private theorem int_not_nominal (arguments : List Argument) :
    ¬ Subtype (.base .int) (nominal 0 arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 arguments.length) ⟨rfl,by simp⟩

private theorem nominal_holds {snapshot : GeneralNominalState.State} {identity name arity : Nat}
    {observation : GeneralCanonicalObservations.Observation}
    (head : Head snapshot identity (.nominal name arity) observation)
    (model : GeneralNominalCommonBridge.Assignment) (valid : observation.Holds model) :
    ∃ arguments, Equivalent (model identity).1 (nominal name arguments) := by
  generalize tagEq : Test.nominal name arity = tag at head
  cases head with
  | scalar => cases tagEq
  | structural => cases tagEq
  | nominal slot descriptor recorded =>
    cases tagEq
    obtain ⟨arguments,_,equal⟩ := valid
    exact ⟨arguments,equal⟩

theorem cut_slice (certificate : PrefixCertificate state) (support : List (Occurrence roles))
    (excluded : kidW ∉ support) : Slice state support (GeneralNominalOutputGrowth.finiteModel 1) := by
  refine ⟨?_,?_⟩
  · rw [certificate.source]
    exact (GeneralNominalOutputGrowthModels.source_models 1 _).mpr
      (GeneralNominalOutputGrowth.finite_prefix_models 1)
  · intro fact member included
    exact certificate.cut fact member (fun dependency => excluded (included kidW dependency))

theorem wrap_necessary (certificate : PrefixCertificate state) (support : List (Occurrence roles))
    (head : HeadSupported state support 2 (.nominal 0 1)) : kidW ∈ support := by
  classical
  by_cases member : kidW ∈ support
  · exact member
  apply False.elim
  have absent := member
  obtain ⟨snapshot,observation,recorded,entailed⟩ := head
  obtain ⟨arguments,equivalent⟩ := nominal_holds recorded _ (entailed _ (cut_slice certificate support absent))
  exact int_not_nominal arguments equivalent.1

theorem wrap_not_grounded (certificate : PrefixCertificate state) : ¬ Grounded reg state kidW := by
  intro grounded
  apply trap_excluded reg state (fun producer => producer = kidW) ?_ ?_ kidW grounded rfl
  · intro producer same
    subst producer
    exact certificate.wrap_open
  · intro producer same
    subst producer
    refine ⟨wrapChild,certificate.generated,certificate.child_open,2,.nominal 0 1,?_,?_⟩
    · have needed := Need.input (registry := reg) (state := state) (focus := wrapChild)
        (⟨0,by decide +kernel⟩) (.nominal 0 1)
      rw [wrap_child_input] at needed
      exact needed certificate.head
    · intro support head
      exact ⟨kidW,wrap_necessary certificate support head,rfl⟩

theorem downstream_head_blocked (certificate : PrefixCertificate state) (support : List (Occurrence roles))
    (supported : Supported reg state support) : ¬ HeadSupported state support 2 (.nominal 0 1) := by
  intro head
  exact wrap_not_grounded certificate (supported kidW (wrap_necessary certificate support head))

/-- A certified nominal descriptor fixes the root test even when alternative
certificates use different child intervals. -/
theorem nominal_test_unique (snapshot : GeneralNominalState.State) (slot : Fin snapshot.base.slots)
    (descriptor : GeneralNominalState.Descriptor snapshot.base.slots)
    (recorded : snapshot.nominals slot = some descriptor) (test : Test)
    (observation : GeneralCanonicalObservations.Observation)
    (head : Head snapshot (snapshot.base.source slot) test observation) :
    test = .nominal descriptor.declaration.name descriptor.arguments.length := by
  generalize identityEq : snapshot.base.source slot = identity at head
  cases head with
  | scalar other base seen =>
    have same := snapshot.base.source_injective identityEq
    subst other
    rw [snapshot.bodies_opaque slot descriptor recorded] at seen
    cases seen
  | structural other kind children seen =>
    have same := snapshot.base.source_injective identityEq
    subst other
    rw [snapshot.bodies_opaque slot descriptor recorded] at seen
    cases seen
  | nominal other actual seen =>
    have same := snapshot.base.source_injective identityEq
    subst other
    have equal := Option.some.inj (recorded.symm.trans seen)
    subst actual
    rfl

theorem first_downstream_decision_blocked (certificate : PrefixCertificate state)
    (focus : Occurrence roles) (index : Fin (roles focus.demand.role).arity)
    (input : (focus.demand.arguments index).1 = 2)
    (current : ∀ test observation, Head state.current.context.state 2 test observation → test = .nominal 0 1) :
    ¬ ∃ support, GeneralNominalDownstreamSupport.DecisionGuard reg state focus support := by
  rintro ⟨support,guard,supported⟩
  have ready := guard.2.1 index
  rw [input] at ready
  obtain ⟨test,observation,head,known⟩ := ready
  have equal := current test observation head
  subst test
  exact downstream_head_blocked certificate support supported known

abbrev nextPacket : Packet roles :=
  ⟨reg,ctx,GeneralNominalDemandMerging.pointSite kidP,p,p_checked,[(1,1)]⟩
abbrev nextP : Occurrence roles := GeneralNominalFeedbackSites.clauseChild nextPacket pp sigP
abbrev nextW : Occurrence roles := GeneralNominalFeedbackSites.clauseChild nextPacket wp sigW

theorem next_bindings : nextPacket.bindings = [(0,(2,2))] := by
  have report : GeneralNominalRecursiveCandidates.report ctx p [(1,1)] = captured src 1 0 0 (2,2) := by
    exact report_exact ctx p 1 (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 (2,2) rfl p_query
  unfold Packet.bindings
  rw [report]
  rfl

theorem next_inputs :
    (∀ index, nextP.demand.arguments index = (2,2)) ∧
    (∀ index, nextW.demand.arguments index = (2,2)) := by
  constructor
  · intro index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simp [nextP,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
      GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
      GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
      next_bindings,GeneralNominalAllocation.occurrences,zero,pp,GeneralDeclarationPatterns.normalize]
  · intro index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simp [nextW,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
      GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
      GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
      next_bindings,GeneralNominalAllocation.occurrences,zero,wp,GeneralDeclarationPatterns.normalize]

theorem first_P_and_W_blocked (certificate : PrefixCertificate state)
    (current : ∀ test observation, Head state.current.context.state 2 test observation → test = .nominal 0 1) :
    (¬ ∃ support, GeneralNominalDownstreamSupport.DecisionGuard reg state nextP support) ∧
    (¬ ∃ support, GeneralNominalDownstreamSupport.DecisionGuard reg state nextW support) := by
  constructor
  · exact first_downstream_decision_blocked certificate nextP ⟨0,by decide +kernel⟩
      (congrArg Prod.fst (next_inputs.1 _)) current
  · exact first_downstream_decision_blocked certificate nextW ⟨0,by decide +kernel⟩
      (congrArg Prod.fst (next_inputs.2 _)) current

theorem first_downstream_packet_blocked (certificate : PrefixCertificate state)
    (packet : Packet roles) (registry : packet.registry = reg) (context : packet.context = state.current.context)
    (index : Fin (roles packet.site.occurrence.demand.role).arity)
    (input : (packet.site.occurrence.demand.arguments index).1 = 2)
    (current : ∀ test observation, Head state.current.context.state 2 test observation → test = .nominal 0 1)
    (support : List (Occurrence roles)) : ¬ GeneralNominalDownstreamSupport.PacketGuard state packet support := by
  intro guard
  apply first_downstream_decision_blocked certificate packet.site.occurrence index input current
  refine ⟨support,?_,?_⟩
  · simpa only [context,registry] using guard.1.2
  · simpa only [registry] using guard.2

local instance : NeZero afterP.current.context.state.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

noncomputable abbrev containerPacket : Packet roles :=
  ⟨reg,afterP.current.context,GeneralNominalFeedbackSites.childSite pk kidC,c,c_checked,[(1,1)]⟩

theorem container_source_guard : GeneralNominalDownstreamSupport.PacketGuard afterP containerPacket [] := by
  apply source_packet
  let descriptor := GeneralNominalOutputGrowthModels.descriptor 1 (1 : Fin src.base.slots) (Nat.le_refl _)
  have original : Head src 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := src) 1 descriptor rfl
  have current : Head afterP.current.context.state 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := afterP.current.context.state) (1 : Fin src.base.slots) descriptor rfl
  have ready : ReadyAt afterP [] 1 := source_ready afterP 1 _ _ _ original current []
  have located : GeneralNominalRecursiveCandidates.arguments afterP.current.context kidC = some [(1,1)] := by
    change GeneralCandidateBoundaryParts.locate src.base [kidC.demand.arguments ⟨0,by decide +kernel⟩] = _
    rw [child_inputs.1]
    have one : GeneralDictionaryBinderLocations.sourceSlot src.base 1 = some (1 : Fin 3) :=
      (GeneralDictionaryBinderLocations.sourceSlot_exact src.base 1 1).mpr rfl
    simp [GeneralCandidateBoundaryParts.locate,one]
    rfl
  have query : GeneralNominalInspection.queries afterP.current.context.state afterP.current.context.interpretation c =
      [.nominal 0 [.variables [0]]] := by
    change GeneralNominalInspection.queries src ctx.interpretation c = _
    simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
      GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source]
  have reads : readsMany afterP.current.context.state
      (GeneralNominalInspection.queries afterP.current.context.state afterP.current.context.interpretation c) [(1,1)] = [1] := by
    rw [query]
    simp only [readsMany.eq_def,List.append_nil]
    rw [GeneralNominalSupport.reads.eq_def]
    change (1 : Fin src.base.slots) :: readsMany afterP.current.context.state [.variables [0]] [(2,2)] = [1]
    rw [readsMany.eq_def]
    simp only [GeneralNominalSupport.reads.eq_def,readsMany.eq_def,List.nil_append,List.append_nil]
    rfl
  have decisions : GeneralNominalSupport.DecisionGuard afterP reg kidC [] := by
    refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
    · intro index
      rw [child_inputs.1 index]
      exact ready
    · intro declaration visible sameRole bounds found slot member
      have same : declaration = c := by
        simp only [reg,List.mem_cons,List.not_mem_nil,or_false] at visible
        rcases visible with rfl | rfl | rfl
        · cases sameRole
        · rfl
        · cases sameRole
      subst declaration
      have equal := Option.some.inj (located.symm.trans found)
      subst bounds
      rw [reads] at member
      have equal := List.mem_singleton.mp member
      subst slot
      exact ready
  exact ⟨⟨decisions.1,decisions.2.1,decisions.2.2 c (by simp [reg]) rfl _ located⟩,decisions⟩

end Yulang.GeneralNominalDownstreamSiblingFixture

namespace Yulang.GeneralNominalDownstreamSiblingFixture
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings
open GeneralNominalDownstreamSupport
open GeneralDeclarationExamples (roles constructors wrap wrap_checked containerChild)
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open CommonNominalFullCarrier
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

abbrev cutContainer : Packet roles :=
  ⟨reg,ctx,GeneralNominalDemandMerging.pointSite kidC,c,c_checked,[(1,1)]⟩

def cutJournal : Tracked roles where
  source := ctx
  current := {
    context := ctx
    packets := [pk,cutContainer,wrapPacket]
    sites := [root,kidC,kidW,kidP,wrapChild].map GeneralNominalDemandMerging.pointSite
    edges := [(root,kidC),(root,kidW),(root,kidP),(kidW,wrapChild)] }
  facts := [.inputs pk [],.outputs pk [],.inputs cutContainer [],.outputs cutContainer [],
    .inputs wrapPacket [],.outputs wrapPacket []]

theorem cut_container_report : GeneralNominalRecursiveCandidates.report ctx c [(1,1)] =
    captured src 1 0 0 (2,2) := by
  apply report_exact ctx c 1 (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 (2,2) rfl
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source,
    GeneralNominalOutputGrowthModels.descriptor]

theorem cut_container_bindings : cutContainer.bindings = [(0,(2,2))] := by
  unfold Packet.bindings
  rw [cut_container_report]
  rfl

theorem cut_container_schema : GeneralNominalPacketSupport.namedSchema cutContainer =
    ⟨[⟨0,.source out,.actual⟩],[],false⟩ := by
  change GeneralNominalRecursiveCandidates.generated reg ctx kidC c c_checked [(1,1)] = _
  unfold GeneralNominalRecursiveCandidates.generated GeneralNominalMaterialization.requests
    GeneralNominalMaterialization.rootRequests
  rw [shared_output.1]
  unfold GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  simp [GeneralNominalMaterialization.rootRequests,GeneralCanonicalChildOrder.canonicalEmit,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    GeneralDeclarationDemands.emitAll,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationPatterns.normalize,src,GeneralNominalOutputGrowthModels.source]

theorem cut_wrap_schema : GeneralNominalPacketSupport.namedSchema wrapPacket =
    ⟨[⟨1,.nominal (.source out) 0 0,.actual⟩,⟨1,.source wrapOutput,.actual⟩],
      [(.source out,.nominal 0 1)],false⟩ := by
  change GeneralNominalRecursiveCandidates.generated reg ctx kidW wrap wrap_checked [(1,1)] = _
  unfold GeneralNominalRecursiveCandidates.generated
  rw [wrap_report]
  unfold GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.rootRequests,shared_output.2,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,bindings,captured,
    wrapOutput,GeneralNominalAllocation.allocation,src,GeneralNominalOutputGrowthModels.source]

private theorem cut_container_inputs (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src model) : GeneralNominalPacketSupport.Inputs cutContainer model := by
  have query : GeneralNominalInspection.queries src ctx.interpretation c = [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
      GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source]
  have original := private_models ctx reg kidC c 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 rfl (2,2) rfl query model valid
  refine ⟨((GeneralNominalPacketSupport.private_exact cutContainer model).mp original.1).2,original.2,?_⟩
  have empty : GeneralNominalPacketSupport.inputSchema cutContainer = {} := by
    unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
    simp [GeneralNominalPacketSupport.inputSchema,GeneralNominalPacketSupport.inputRequests,
      GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil,List.mergeSort_singleton,GeneralDeclarationDemands.emitAll,
      GeneralNominalMaterialization.generated]
  rw [empty]
  exact GeneralNominalMaterialization.empty_models ..

private theorem cut_wrap_inputs (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src model) : GeneralNominalPacketSupport.Inputs wrapPacket model := by
  have query : GeneralNominalInspection.queries src ctx.interpretation wrap = [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
      GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source]
  have original := private_models ctx reg kidW wrap 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 rfl (2,2) rfl query model valid
  refine ⟨((GeneralNominalPacketSupport.private_exact wrapPacket model).mp original.1).2,original.2,?_⟩
  have empty : GeneralNominalPacketSupport.inputSchema wrapPacket = {} := by
    unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
    simp [GeneralNominalPacketSupport.inputSchema,GeneralNominalPacketSupport.inputRequests,
      GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil,List.mergeSort_singleton,GeneralDeclarationDemands.emitAll,
      GeneralDeclarationDemands.emit,GeneralNominalMaterialization.inputRequests,List.ofFn_succ,
      GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated]
  rw [empty]
  exact GeneralNominalMaterialization.empty_models ..

end Yulang.GeneralNominalDownstreamSiblingFixture

namespace Yulang.GeneralNominalDownstreamSiblingFixture
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings GeneralNominalDownstreamSupport
open GeneralDeclarationExamples (roles constructors wrap wrap_checked containerChild)
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

private theorem cut_container_outputs (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src model) (same : Equivalent (model out).1 (model 2).1) :
    GeneralNominalPacketSupport.Outputs cutContainer model := by
  change GeneralNominalMaterialization.Models src c _ (GeneralNominalRecursiveCandidates.report ctx c [(1,1)])
    (GeneralNominalPacketSupport.namedSchema cutContainer) model
  rw [cut_container_schema,cut_container_report]
  have argument := nominal_argument_bounds src model valid 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 (2,2) rfl
  refine ⟨(by intro test impossible; cases impossible),?_,?_,?_⟩
  · intro use member
    have equal := List.mem_singleton.mp member
    subst use
    refine ⟨⟨_,.source out⟩,?_⟩
    intro actual observed
    cases observed
    change GeneralNominalMaterialization.VariableHolds c
      (GeneralNominalPacketSupport.capture cutContainer) model 0 .actual (model out).1
    change GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalAllocation.capture src reg kidC.identity c.id cutContainer.bindings).inputs 0) (model out).1
    rw [cut_container_bindings]
    exact ⟨same.2,same.1⟩
  · intro first one last two _ _ _ a b ha hb
    have aeq := List.mem_singleton.mp one
    have beq := List.mem_singleton.mp two
    subst first; subst last
    cases ha; cases hb
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro use member captured capturedMember _ _ origin recorded a b ha hb
    have ue := List.mem_singleton.mp member
    have ce := List.mem_singleton.mp capturedMember
    subst use; subst captured
    have oe : Origin.nominal (.source 1) 0 0 = origin := Option.some.inj recorded
    subst origin
    cases ha
    have fits := argument.2 b hb
    exact ⟨subtype_trans same.1 fits.1,subtype_trans fits.2 same.2⟩

theorem cut_journal_facts : ∀ fact ∈ cutJournal.facts, kidW ∉ fact.dependencies →
    fact.Holds (GeneralNominalOutputGrowth.finiteModel 1) := by
  let model := GeneralNominalOutputGrowth.finiteModel 1
  have valid := (GeneralNominalOutputGrowthModels.source_models 1 model).mpr
    (GeneralNominalOutputGrowth.finite_prefix_models 1)
  have parent := (GeneralNominalPacketSupport.packet_exact pk model).mp (p_branch model valid)
  have above : 2 < out := GeneralNominalIdentities.source_above_seed _ _
  have same : Equivalent (model out).1 (model 2).1 := by
    have zero : 1+1-out = 0 := by omega
    change Equivalent (GeneralNominalOutputGrowth.tower (1+1-out)) (GeneralNominalOutputGrowth.tower (1+1-2))
    rw [zero]
    exact ⟨subtype_refl _,subtype_refl _⟩
  intro fact member absent
  change fact ∈ [Fact.inputs pk [],.outputs pk [],.inputs cutContainer [],.outputs cutContainer [],
    .inputs wrapPacket [],.outputs wrapPacket []] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact parent.2.1
  · exact parent.2.2
  · exact cut_container_inputs model valid
  · exact cut_container_outputs model valid same
  · exact cut_wrap_inputs model valid
  · exact False.elim (absent (by simp [Fact.dependencies,wrapPacket,GeneralNominalDemandMerging.pointSite]))

private theorem container_equation (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalPacketSupport.Outputs cutContainer model) : Equivalent (model out).1 (model 2).1 := by
  change GeneralNominalMaterialization.Models src c _ _ (GeneralNominalPacketSupport.namedSchema cutContainer) model at valid
  rw [cut_container_schema] at valid
  have bound := (valid.2.1 ⟨0,.source out,.actual⟩ (by simp)).2 (model out).1 (.source out)
  change GeneralNominalCaptureMerges.Fits model
    ((GeneralNominalAllocation.capture src reg kidC.identity c.id cutContainer.bindings).inputs 0) (model out).1 at bound
  rw [cut_container_bindings] at bound
  exact ⟨bound.2,bound.1⟩

private theorem wrap_equation (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalPacketSupport.Outputs wrapPacket model) :
    Equivalent (model out).1 (nominal 0 [.inl (model wrapOutput).1]) := by
  change GeneralNominalMaterialization.Models src wrap _ _ (GeneralNominalPacketSupport.namedSchema wrapPacket) model at valid
  rw [cut_wrap_schema] at valid
  obtain ⟨arguments,size,equal⟩ := (valid.1 (.source out,.nominal 0 1) (by simp)).2 _ (.source _)
  have projected := valid.2.1 ⟨1,.nominal (.source out) 0 0,.actual⟩ (by simp)
  cases arguments with
  | nil => cases size
  | cons argument rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at size; omega)
    subst rest
    cases argument with
    | inl value =>
      have captured := projected.2 value (.nominal (.source _) equal rfl)
      change Equivalent value (model wrapOutput).1 at captured
      have congruence := GeneralNominalState.singleton_nominal_congr 0 _ _ captured
      exact ⟨subtype_trans equal.1 congruence.1,subtype_trans congruence.2 equal.2⟩
    | inr row =>
      obtain ⟨actual,seen⟩ := projected.1
      cases seen with
      | nominal parent compared found =>
        cases parent
        have incompatible := ((nominal_regular_invariant_exact _ _ _ _).mp
          (subtype_trans equal.2 compared.1)).2.2 0 (.inr row) (.inl actual) rfl found
        exact False.elim incompatible

private theorem full_equation (model : GeneralNominalCommonBridge.Assignment) (valid : AllModels cutJournal model) :
    Equivalent (model 2).1 (nominal 0 [.inl (model wrapOutput).1]) := by
  have first := container_equation model (valid.2 (.outputs cutContainer []) (by simp [cutJournal]))
  have last := wrap_equation model (valid.2 (.outputs wrapPacket []) (by simp [cutJournal]))
  exact ⟨subtype_trans first.2 last.1,subtype_trans last.2 first.1⟩

end Yulang.GeneralNominalDownstreamSiblingFixture

namespace Yulang.GeneralNominalDownstreamSiblingFixture
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings GeneralNominalDownstreamSupport
open GeneralDeclarationExamples (roles constructors wrap wrap_checked containerChild)
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier

theorem wrap_output_above : 2 < wrapOutput := GeneralNominalIdentities.source_above_seed _ _

private def witnessDescriptor : GeneralNominalState.Descriptor (wrapOutput+2) :=
  ⟨0,⟨[.type],0⟩,[.type (⟨wrapOutput,by omega⟩,⟨wrapOutput,by omega⟩)],rfl⟩

private def witnessState : GeneralNominalState.State where
  base := GeneralNominalOutputGrowthModels.base wrapOutput
  view := GeneralNominalOutputGrowthModels.view wrapOutput
  constructors := constructors
  nominals := fun slot => if slot.val = 2 then some witnessDescriptor else none
  catalogue := by
    intro slot descriptor recorded
    split at recorded
    · have same := Option.some.inj recorded; subst descriptor; rfl
    · cases recorded
  bodies_opaque := by intro _ _ _; rfl

private def witnessSlot : Fin witnessState.base.slots := ⟨2,by have above := wrap_output_above; change 2 < wrapOutput+2; omega⟩

theorem cut_journal_head : Available cutJournal 2 (.nominal 0 1) := by
  refine ⟨witnessState,.nominal witnessState.base witnessSlot witnessDescriptor,?_,?_⟩
  · exact Head.nominal (snapshot := witnessState) witnessSlot witnessDescriptor (by simp [witnessState,witnessSlot])
  · intro model slice
    have equal := full_equation model ((pool_exact cutJournal model).mp slice)
    refine ⟨[.inl (model wrapOutput).1],?_,equal⟩
    exact .cons ⟨subtype_refl _,subtype_refl _⟩ .nil

private theorem wrap_distinct_container : kidW.identity ≠ kidC.identity := by decide +kernel
private theorem root_distinct_container : root.identity ≠ kidC.identity := by decide +kernel
private theorem child_distinct_container : wrapChild.identity ≠ kidC.identity := by decide +kernel

private theorem cut_alias_identity (related : Alias cutJournal.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

private theorem cut_discharged (focus : Occurrence roles) (done : Discharged cutJournal.current focus) :
    focus.identity = kidC.identity := by
  induction done with
  | packet packet member children ih =>
    change packet ∈ [pk,cutContainer,wrapPacket] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact False.elim (wrap_distinct_container (ih kidW (by rw [p_children]; simp)))
    · rfl
    · exact False.elim (child_distinct_container (ih wrapChild (by rw [wrap_children]; simp)))
  | alias first last _ _ related _ ih => exact (cut_alias_identity related).symm.trans ih

theorem cut_journal_certificate : PrefixCertificate cutJournal := by
  have wrapOpen : ¬ Discharged cutJournal.current kidW :=
    fun done => wrap_distinct_container (cut_discharged kidW done)
  have childOpen : ¬ Discharged cutJournal.current wrapChild :=
    fun done => child_distinct_container (cut_discharged wrapChild done)
  refine ⟨rfl,wrapOpen,childOpen,?_,cut_journal_head,cut_journal_facts⟩
  exact .child (.root wrapOpen) (by simp [cutJournal]) childOpen

theorem concrete_wrap_not_grounded : ¬ Grounded reg cutJournal kidW :=
  wrap_not_grounded cut_journal_certificate

theorem concrete_downstream_head_blocked (support : List (Occurrence roles))
    (supported : Supported reg cutJournal support) : ¬ HeadSupported cutJournal support 2 (.nominal 0 1) :=
  downstream_head_blocked cut_journal_certificate support supported

end Yulang.GeneralNominalDownstreamSiblingFixture

namespace Yulang.GeneralNominalDownstreamSiblingFixture
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings GeneralNominalDownstreamSupport
open GeneralDeclarationExamples (roles constructors wrap wrap_checked containerChild)
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier

local instance : NeZero ctx.state.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

private theorem wrap_outputs_of_equation (model : GeneralNominalCommonBridge.Assignment)
    (equation : Equivalent (model out).1 (nominal 0 [.inl (model wrapOutput).1])) :
    GeneralNominalPacketSupport.Outputs wrapPacket model := by
  change GeneralNominalMaterialization.Models src wrap _
    (GeneralNominalRecursiveCandidates.report ctx wrap [(1,1)]) (GeneralNominalPacketSupport.namedSchema wrapPacket) model
  rw [cut_wrap_schema,wrap_report]
  have observed : Observes model (.nominal (.source out) 0 0) (model wrapOutput).1 :=
    .nominal (.source _) equation rfl
  have unique : ∀ actual, Observes model (.nominal (.source out) 0 0) actual → Equivalent actual (model wrapOutput).1 :=
    fun actual seen => nominal_observation_unique model (.argument (.source out) 0 0) actual _ seen observed
  have all : ∀ use ∈ [({name := 1,origin := .nominal (.source out) 0 0,mode := .actual} : GeneralNominalMaterialization.Use),
      ⟨1,.source wrapOutput,.actual⟩], ∀ actual, Observes model use.origin actual → Equivalent actual (model wrapOutput).1 := by
    intro use member actual seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact unique actual seen
    · cases seen; exact ⟨subtype_refl _,subtype_refl _⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have same := List.mem_singleton.mp member; subst test
    refine ⟨⟨_,.source out⟩,?_⟩
    intro actual seen; cases seen
    exact ⟨[.inl (model wrapOutput).1],rfl,equation⟩
  · intro use member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨_,observed⟩,fun actual seen => unique actual seen⟩
    · exact ⟨⟨_,.source wrapOutput⟩,fun actual seen => by cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
  · intro first one last two _ _ _ a b ha hb
    exact ⟨subtype_trans (all first one a ha).1 (all last two b hb).2,
      subtype_trans (all last two b hb).1 (all first one a ha).2⟩
  · intro use member captured present same _
    have equal := List.mem_singleton.mp present; subst captured
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> cases same

def journalModel : GeneralNominalCommonBridge.Assignment :=
  fun identity => if identity = out then (GeneralNominalOutputGrowth.tower 1,Common.rowEmpty)
    else GeneralNominalOutputGrowth.finiteModel 2 identity

private theorem out_above : 2 < out := GeneralNominalIdentities.source_above_seed _ _
private theorem out_distinct_wrap_output : out ≠ wrapOutput := by decide +kernel

private theorem journal_source_model : GeneralNominalState.Models src journalModel := by
  apply (GeneralNominalOutputGrowthModels.source_models 1 journalModel).mpr
  intro index bound
  have one : index ≠ out := by have above := out_above; omega
  have two : index+1 ≠ out := by have above := out_above; omega
  change Equivalent (journalModel index).1 (nominal 0 [.inl (journalModel (index+1)).1])
  simp only [journalModel,ite_eq_right one,ite_eq_right two]
  exact GeneralNominalOutputGrowth.finite_prefix_models 2 index (by omega)

private theorem journal_container_equation : Equivalent (journalModel out).1 (journalModel 2).1 := by
  have two : 2 ≠ out := by have above := out_above; omega
  simp only [journalModel,ite_eq_left rfl,ite_eq_right two]
  exact ⟨subtype_refl _,subtype_refl _⟩

private theorem journal_wrap_equation : Equivalent (journalModel out).1 (nominal 0 [.inl (journalModel wrapOutput).1]) := by
  have different := Ne.symm out_distinct_wrap_output
  have zero : 2+1-wrapOutput = 0 := by have above := wrap_output_above; omega
  simp only [journalModel,ite_eq_left rfl,ite_eq_right different,GeneralNominalOutputGrowth.finiteModel,zero]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem cut_journal_all_models : AllModels cutJournal journalModel := by
  refine ⟨journal_source_model,?_⟩
  have parent := (GeneralNominalPacketSupport.packet_exact pk journalModel).mp
    (p_branch journalModel journal_source_model)
  intro fact member
  change fact ∈ [Fact.inputs pk [],.outputs pk [],.inputs cutContainer [],.outputs cutContainer [],
    .inputs wrapPacket [],.outputs wrapPacket []] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact parent.2.1
  · exact parent.2.2
  · exact cut_container_inputs journalModel journal_source_model
  · exact cut_container_outputs journalModel journal_source_model journal_container_equation
  · exact cut_wrap_inputs journalModel journal_source_model
  · exact wrap_outputs_of_equation journalModel journal_wrap_equation

theorem cut_journal_exact : GeneralNominalSupportSteps.Exact cutJournal := by
  intro model
  constructor
  · intro valid
    refine ⟨valid.1,?_⟩
    have parent := (GeneralNominalPacketSupport.packet_exact pk model).mp
      (valid.2.1 pk (by simp [cutJournal]))
    have container := (GeneralNominalPacketSupport.packet_exact cutContainer model).mp
      (valid.2.1 cutContainer (by simp [cutJournal]))
    have wrapValid := (GeneralNominalPacketSupport.packet_exact wrapPacket model).mp
      (valid.2.1 wrapPacket (by simp [cutJournal]))
    intro fact member
    change fact ∈ [Fact.inputs pk [],.outputs pk [],.inputs cutContainer [],.outputs cutContainer [],
      .inputs wrapPacket [],.outputs wrapPacket []] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact parent.2.1
    · exact parent.2.2
    · exact container.2.1
    · exact container.2.2
    · exact wrapValid.2.1
    · exact wrapValid.2.2
  · intro valid
    refine ⟨valid.1,?_,?_⟩
    · intro packet member
      change packet ∈ [pk,cutContainer,wrapPacket] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals apply (GeneralNominalPacketSupport.packet_exact _ model).mpr
      all_goals exact ⟨valid.1,valid.2 (.inputs _ []) (by simp [cutJournal]),
        valid.2 (.outputs _ []) (by simp [cutJournal])⟩
    · intro site member
      obtain ⟨focus,_,rfl⟩ := List.mem_map.mp member
      exact point_holds focus model

theorem cut_journal_models : Models cutJournal.current journalModel :=
  (cut_journal_exact journalModel).mpr cut_journal_all_models

end Yulang.GeneralNominalDownstreamSiblingFixture

namespace Yulang.GeneralNominalDownstreamSiblingFixture
open GeneralNominalSupportSiblings

theorem cut_journal_no_feedback_cycle (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle cutJournal.current identity := by
  let depth : Nat → Nat := fun source => if source = out then 1 else 2+1-source
  apply GeneralNominalOutputGrowthModels.feedback_acyclic cutJournal.current journalModel cut_journal_models depth
  · intro source
    by_cases same : source = out <;>
      simp [journalModel,depth,same,GeneralNominalOutputGrowth.finiteModel] <;> rfl
  · rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩
    exact Fin.elim0 kind

end Yulang.GeneralNominalDownstreamSiblingFixture
