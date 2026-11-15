import Yulang.GeneralDictionaryDefaultCollapseReplay213
import Yulang.GeneralDictionaryDefaultTerminalReduction212
import Yulang.GeneralDictionarySemanticCollapseOutputExample

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryDefaultPointRegression213
open GeneralDictionarySemanticCollapseExample GeneralDictionarySemanticCollapseOutputExample
open GeneralDictionaryDefaultNonpointTerminal210
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier

abbrev site := GeneralNominalDemandMerging.pointSite outputRoot
abbrev center : Site GeneralDeclarationExamples.roles := ⟨outputRoot,fun _ => 0⟩
abbrev before := oldPlan shape registry site declaration checked center rfl
abbrev after := newPlan shape registry site declaration checked center rfl

theorem before_bindings : before.packet.bindings = [(7,3,3),(7,3,3)] := by
  change bindings source (GeneralNominalRecursiveCandidates.report context declaration bounds) = _
  rw [report_exact]; rfl

theorem after_bindings : after.packet.bindings = [(7,3,3)] := by
  change bindings revision.snapshot (GeneralNominalRecursiveCandidates.report
    (GeneralDictionarySemanticCollapseBranch.currentContext revision) declaration [(shape.root,shape.root)]) = _
  rw [(GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).2]; rfl

theorem before_binder : before.binder 7 = GeneralNominalCenters.fresh 3 0 42 8 7 0 := by
  simp only [Plan.binder]
  change (if 7 ∈ declaration.outputNames then _ else _) = _
  simp only [GeneralDeclarations.Declaration.outputNames,List.map_nil,List.not_mem_nil,ite_false]
  unfold GeneralNominalPacketSupport.capture
  rw [before_bindings]
  decide +kernel

theorem after_binder : after.binder 7 = 3 := by
  simp only [Plan.binder]
  change (if 7 ∈ declaration.outputNames then _ else _) = _
  simp only [GeneralDeclarations.Declaration.outputNames,List.map_nil,List.not_mem_nil,ite_false]
  unfold GeneralNominalPacketSupport.capture
  rw [after_bindings]
  rfl

theorem binder_changes : before.binder 7 ≠ after.binder 7 := by
  rw [before_binder,after_binder]
  decide +kernel

theorem before_value : (model (before.binder 7)).1 = leafValue := by
  rw [before_binder]
  rfl

theorem head_schema : before.headSchema =
  ⟨[⟨7,GeneralDictionarySemanticCollapse.leaf shape,.actual⟩],
    [(.source 0,.nominal 0 1),(GeneralDictionarySemanticCollapse.parent shape,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  change GeneralNominalMaterialization.schemas (GeneralNominalInspection.queries source interpretation declaration) _ _ _ = _
  rw [queries]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralDictionarySemanticCollapse.query,
    before,oldPlan,center,shape,GeneralDictionarySemanticCollapse.parent,GeneralDictionarySemanticCollapse.leaf,
    outputRoot,GeneralDeclarationExamples.roles,GeneralDeclarationExamples.outputRole,source,
    GeneralNominalIntervalExamples.base]

theorem head_holds : before.SchemaHolds before.headSchema model := by
  rw [head_schema]
  constructor
  · intro test member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨⟨_,.source 0⟩,?_⟩
      intro value seen; cases seen
      exact ⟨[.inl innerValue],rfl,subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,observed_parent⟩,fun value seen => ⟨[.inl leafValue],rfl,parent_unique value seen⟩⟩
  · intro entry member
    cases List.mem_singleton.mp member
    change GeneralNominalOriginTerms.Same model _ (.source (before.binder 7))
    refine ⟨⟨_,observed_leaf⟩,⟨_,.source _⟩,?_⟩
    intro a b one two; cases two
    rw [before_value]
    exact leaf_unique a one

theorem input_holds : before.input.Holds model := by
  intro index
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem fits : ∀ name ∈ declaration.inputNames,
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture before.packet).inputs name)
      (model (before.binder name)).1 := by
  intro name member
  cases List.mem_singleton.mp member
  unfold GeneralNominalPacketSupport.capture
  rw [before_bindings,before_value]
  exact ⟨(GeneralDictionarySemanticCollapseAllocationExample.endpoints registry 0 declaration names).1.1,
    (GeneralDictionarySemanticCollapseAllocationExample.endpoints registry 0 declaration names).2.2⟩

theorem outputs : GeneralNominalCenteredHeadMatStepPackets.Outputs before model := by
  intro equation member
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema at member
  rw [GeneralDictionaryDefaultTerminalOutputs210.terminal_requests before rfl] at member
  change equation ∈ (GeneralNominalCenteredHeadMatSchemas.generated source.constructors interpretation
    (GeneralNominalMaterialization.rootRequests declaration outputRoot)).equations at member
  rw [root_request] at member
  change equation ∈ [⟨3,.actual,.variable 7⟩] at member
  cases List.mem_singleton.mp member
  change Equivalent (model 3).1 (model (before.binder 7)).1
  rw [before_value]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem old_holds : GeneralNominalCenteredHeadMatStepPackets.Holds before model := by
  apply (GeneralDictionaryDefaultTerminalReduction212.packet_iff (plan := before) rfl).mpr
  exact ⟨⟨GeneralDictionarySemanticCollapseOutputExample.private_models,old_branch.2.1⟩,
    ⟨input_holds,fits,head_holds⟩,outputs⟩

theorem replayed : GeneralNominalCenteredHeadMatStepPackets.Holds after model :=
  GeneralDictionaryDefaultCollapseReplay213.replay shape registry site declaration checked center rfl
    queries names rfl model old_holds revised_models

theorem semantic_binder_agreement : Equivalent (model (before.binder 7)).1 (model (after.binder 7)).1 := by
  rw [before_value,after_binder]
  exact ⟨subtype_refl _,subtype_refl _⟩
end Yulang.GeneralDictionaryDefaultPointRegression213
