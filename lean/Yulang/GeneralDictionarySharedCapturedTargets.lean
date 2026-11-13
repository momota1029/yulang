import Yulang.GeneralDictionarySharedOutputBinderScope
import Yulang.GeneralDictionaryRecursiveObstruction

/-! Concrete source capture and emitted target mapping for the checked
captured-input proposal. This is not yet a Shared execution or resumed consumer. -/
namespace Yulang.GeneralDictionarySharedCapturedTargets
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDeclarationExamples (roles constructors)
abbrev source := GeneralNominalOutputGrowthModels.source 1
abbrev context := GeneralNominalOutputGrowthModels.context 1
local instance : NeZero source.base.slots := ⟨by change 3 ≠ 0; omega⟩
abbrev registry : Registry := ⟨constructors,roles,
  [capturedProposal,GeneralDictionaryRecursiveObstruction.declaration]⟩
abbrev root : Occurrence roles := ⟨0,⟨0,fun _ => (0,0),[],by intro _ member; cases member⟩⟩
abbrev packet : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,capturedProposal,
    captured_proposal_checked,[(0,0)]⟩
abbrev origin : Origin := .nominal (.nominal (.source 0) 0 0) 0 0

theorem queries : GeneralNominalInspection.queries source context.interpretation capturedProposal =
    [.nominal 0 [.nominal 0 [.variables [0]]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    source,GeneralNominalOutputGrowthModels.source]

theorem captures : (GeneralNominalPacketSupport.report packet).captures = [⟨0,(2,2),some origin⟩] := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [queries]
  simp only [inspectMany.eq_def]
  rw [inspect.eq_def]
  change (Report.append
    (Report.visit (0,0) none (.nominal 0 1)
      (inspectMany source [.nominal 0 [.variables [0]]] [(1,1)]
        (fun index => some (.nominal (.source 0) 0 index)) 0))
    {}).captures = _
  rw [inspectMany.eq_def]
  dsimp only
  rw [inspect.eq_def]
  change (Report.append
    (Report.visit (0,0) none (.nominal 0 1)
      (Report.append
        (Report.visit (1,1) (some (.nominal (.source 0) 0 0)) (.nominal 0 1)
          (inspectMany source [.variables [0]] [(2,2)]
            (fun index => some (.nominal (.nominal (.source 0) 0 0) 0 index)) 0))
        (inspectMany source [] [] (fun index => some (.nominal (.source 0) 0 index)) 1)))
    {}).captures = _
  simp only [inspectMany.eq_def,inspect.eq_def]
  rfl

theorem bindings : packet.bindings = [(0,(2,2))] := by
  unfold Packet.bindings
  change GeneralNominalRecursiveInspection.bindings source (GeneralNominalPacketSupport.report packet) = _
  simp only [GeneralNominalRecursiveInspection.bindings,captures,List.map_cons,List.map_nil]
  rfl

theorem producer_signature : producerOnInput.Signature roles := by
  exact captured_proposal_checked.signature.2.2.2 producerOnInput (by simp)

theorem consumer_signature : consumerOnInput.Signature roles := by
  exact captured_proposal_checked.signature.2.2.2 consumerOnInput (by simp)

abbrev producer := GeneralNominalFeedbackSites.clauseChild packet producerOnInput producer_signature
abbrev consumer := GeneralNominalFeedbackSites.clauseChild packet consumerOnInput consumer_signature

theorem capture_input : (GeneralNominalPacketSupport.capture packet).inputs 0 = (2,2) := by
  unfold GeneralNominalPacketSupport.capture
  rw [bindings]
  simp [GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences]

abbrev target : Nat := (GeneralNominalAllocation.allocation (roles := roles) source registry root.identity
  capturedProposal.id producerOnInput).outputs 111

theorem producer_output : producer.demand.outputs = [⟨1,target⟩] := by
  unfold producer GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame
    GeneralDictionaryEmissionPlans.occurrence GeneralDeclarationDemands.emit
  simp [GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.outputTarget,
    producerOnInput,GeneralNominalAllocation.frame,
    GeneralDeclarationPatterns.normalize,Declaration.outputNames,target]
  rfl

theorem consumer_input : ∀ index, consumer.demand.arguments index = (2,2) := by
  intro index
  unfold consumer GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame
    GeneralDictionaryEmissionPlans.occurrence GeneralDeclarationDemands.emit
  change Fin 1 at index
  have zero : index = 0 := Fin.ext (by have := index.isLt; omega)
  subst index
  change (GeneralNominalPacketSupport.capture packet).inputs 0 = _
  exact capture_input

theorem output_use :
    (⟨0,.source target,.actual⟩ : GeneralNominalMaterialization.Use) ∈
      (GeneralNominalPacketSupport.namedSchema packet).variables := by
  have sorted : GeneralCanonicalChildOrder.canonicalRequirements capturedProposal.requirements =
      [producerOnInput,consumerOnInput] := by
    unfold GeneralCanonicalChildOrder.canonicalRequirements
    exact List.mergeSort_of_pairwise (by decide +kernel)
  have canon : GeneralCanonicalChildOrder.canonicalDeclaration capturedProposal = capturedProposal := by
    change {capturedProposal with requirements :=
      GeneralCanonicalChildOrder.canonicalRequirements capturedProposal.requirements} = capturedProposal
    rw [sorted]
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
    GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canon]
  simp [GeneralNominalMaterialization.rootRequests,root,capturedProposal,producerOnInput,consumerOnInput,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    List.ofFn_succ,GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationDemands.outputTarget,Declaration.outputNames,target,
    GeneralNominalDemandMerging.pointSite,source,GeneralNominalOutputGrowthModels.source,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationDemands.childDemand]

/-- Materialization proves value equality, not equality of allocated identities. -/
theorem output_equals_captured (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalPacketSupport.Outputs packet model) :
    CommonNominalFullCarrier.Equivalent (model target).1 (model 2).1 := by
  have same := GeneralNominalSharedCaptures.point_use valid output_use rfl
    (by simp [Declaration.outputNames]) capture_input
  exact same.2.2 _ _ (.source target) (.source 2)

theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact captured_proposal_checked
  · exact GeneralDictionaryRecursiveObstruction.declaration_checked

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,⟨rfl,(GeneralNominalOutputGrowthModels.metadata 1).2⟩,?_,?_,
    (GeneralNominalOutputGrowthModels.initial_source 1).below_seed,rfl⟩
  · constructor
    · intro index
      have present := GeneralNominalOutputGrowthModels.source_member 1 (0 : Fin source.base.slots)
      exact ⟨present,present⟩
    · intro output member; cases member
  · intro model valid index
    exact CommonNominalFullCarrier.subtype_refl _

theorem source_model : GeneralNominalState.Models source (GeneralNominalOutputGrowth.finiteModel 1) :=
  (GeneralNominalOutputGrowthModels.source_models 1 _).mpr
    (GeneralNominalOutputGrowth.finite_prefix_models 1)

theorem captured_unknown : ¬ GeneralNominalState.Known source 2 := by
  rintro ⟨slot,equal,head | ⟨descriptor,recorded⟩⟩
  · exact head rfl
  · have same : slot = (2 : Fin 3) := Fin.ext equal
    subst slot
    cases recorded

end Yulang.GeneralDictionarySharedCapturedTargets
