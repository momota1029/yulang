import Yulang.GeneralDictionarySharedCapturedModel
import Yulang.GeneralNominalSharedPositive

/-! Concrete readiness and inherited-input coherence for the captured proposal.
The coherence proof quantifies over every packet model, not just our witness. -/
namespace Yulang.GeneralDictionarySharedCapturedGuards
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralNominalSharedCaptures GeneralNominalRecursiveCandidates
open GeneralDeclarationExamples (roles)
local instance : NeZero source.base.slots := ⟨by change 3 ≠ 0; omega⟩

theorem located : arguments context root = some [(0,0)] := by decide +kernel

theorem prepared : Prepared registry context root capturedProposal captured_proposal_checked := by
  refine ⟨initial_source.metadata,initial_source.linked,
    GeneralNominalSourceFormation.initial_fresh context initial_source root.identity,
    [(0,0)],located,?_,?_,model,branch_models⟩
  · change Finished (GeneralNominalPacketSupport.report packet)
    rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro output h; cases h),?_⟩
    change (GeneralNominalPacketSupport.namedSchema packet).unknown = false
    rw [schema_exact]

theorem root_ready : ¬ GeneralNominalState.RootPending source root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalOutputGrowthModels.descriptor 1 0 (by decide +kernel),rfl⟩⟩

theorem survivor : Survivor registry context root capturedProposal.id packet.children :=
  ⟨root_ready,capturedProposal,by simp,captured_proposal_checked,rfl,rfl,
    [(0,0)],located,prepared,rfl⟩

theorem inherited : (inheritedReport packet).captures = [⟨0,(2,2),some origin⟩] := by
  unfold inheritedReport
  rw [queries]
  simp only [inspectMany.eq_def]
  rw [inspect.eq_def]
  change (Report.append
    (Report.visit (0,0) (some (.source 0)) (.nominal 0 1)
      (inspectMany source [.nominal 0 [.variables [0]]] [(1,1)]
        (fun index => some (.nominal (.source 0) 0 index)) 0)) {}).captures = _
  rw [inspectMany.eq_def]
  dsimp only
  rw [inspect.eq_def]
  change (Report.append
    (Report.visit (0,0) (some (.source 0)) (.nominal 0 1)
      (Report.append
        (Report.visit (1,1) (some mid) (.nominal 0 1)
          (inspectMany source [.variables [0]] [(2,2)]
            (fun index => some (.nominal mid 0 index)) 0))
        (inspectMany source [] [] (fun index => some (.nominal (.source 0) 0 index)) 1))) {}).captures = _
  simp only [inspectMany.eq_def,inspect.eq_def]
  rfl

theorem usable : Usable packet 0 origin :=
  GeneralNominalSharedPositive.single_capture_usable packet 0 (2,2) origin captures inherited
    (by rw [report_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem generation (state : GeneralNominalSupport.Tracked roles) : GenerationGuard state packet := by
  intro name needed
  have input := GeneralDictionarySharedOutputBinderScope.needed_is_input packet name needed
  have zero : name = 0 := by
    simpa [packet,capturedProposal,Declaration.inputNames,Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] using input
  subst name
  exact ⟨origin,usable⟩

theorem input_schema : GeneralNominalPacketSupport.inputSchema packet =
    { variables := [⟨0,.nominal (.source lo) 0 0,.actual⟩,
                    ⟨0,.nominal (.source hi) 0 0,.actual⟩],
      tests := [(.source lo,.nominal 0 1),(.source hi,.nominal 0 1)] } := by
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical]
  simp [root,capturedProposal,producerOnInput,consumerOnInput,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,GeneralDeclarationPatterns.normalize,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,lo,hi,
    GeneralNominalDemandMerging.pointSite,source,GeneralNominalOutputGrowthModels.source,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval]

theorem coherent : InputCoherence packet := by
  intro entry member actual
  have zero : entry.name = 0 := by
    rw [input_schema] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  refine ⟨origin,zero ▸ usable,?_⟩
  intro assignment valid
  have inputs := GeneralNominalPacketSupport.outputs_inputs packet assignment valid.2.2
  have cap : (⟨0,(2,2),some origin⟩ : Capture source) ∈
      (GeneralNominalPacketSupport.report packet).captures := by rw [captures]; simp
  have anchor : (origin,(2,2)) ∈ (GeneralNominalPacketSupport.report packet).anchors := by
    rw [report_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  exact retained_use inputs member actual ⟨0,(2,2),some origin⟩ cap zero rfl
    (valid.2.1.1 _ anchor).1

end Yulang.GeneralDictionarySharedCapturedGuards
