import Yulang.GeneralNominalNonleafChild193
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafReuse193
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193 GeneralNominalNonleafSafety193 GeneralNominalNonleafAdministrative193 GeneralNominalNonleafChild193
open GeneralNominalExamples (registry displayRoot displayChild model intDisplay)
open GeneralDeclarationExamples (roles)
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters CommonNominalFullCarrier
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadOutputs GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel

theorem query : GeneralNominalInspection.queries current.state current.interpretation intDisplay = [.scalar .int] := by
  change GeneralNominalInspection.queries current.state GeneralNominalExamples.interpretation intDisplay = _
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize]
  change GeneralNominalInspection.translate GeneralDeclarationExamples.constructors GeneralNominalExamples.interpretation (.app 2 []) = _
  simp [GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_exact : report current intDisplay [((1 : Fin 2),(1 : Fin 2))] =
    { inspected := [((1 : Fin 2),(1 : Fin 2))], checked := [((1 : Fin 2),(1 : Fin 2)),((1 : Fin 2),(1 : Fin 2))] } := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,
    show current.state.nominals (1 : Fin 2) = none from rfl,
    show current.state.view.heads (1 : Fin 2) = .scalar .int from rfl]

theorem packet_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models current.state assignment) : childPacket.Holds assignment := by
  change _ ∧ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.Compatible]
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.merges,Declaration.inputNames,
        normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]
  · change GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema childPlan.packet) assignment
    rw [GeneralNominalHeadLeafPlan189.named_schema_empty childPlan rfl rfl]
    exact GeneralNominalMaterialization.empty_models ..

theorem committed : GeneralNominalFeedbackSteps.Committed finish.core.erased.current childPacket := by
  constructor
  · intro assignment valid
    exact packet_models assignment valid.1
  · intro child member
    change child ∈ childPlan.packet.children at member
    rw [GeneralNominalHeadLeafPlan189.children_empty childPlan rfl] at member
    cases member

theorem head_schema : childPlan.headSchema = { tests := [(.source 1,.scalar .int)] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,childPlan,centerSite,List.ofFn_succ]

theorem head_equations : HeadEquations childPlan model := by
  refine ⟨?_,?_,?_⟩
  · intro index; exact ⟨subtype_refl _,subtype_refl _⟩
  · intro name member
    simp [Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at member
  · rw [head_schema]
    constructor
    · intro test member
      cases List.mem_singleton.mp member
      exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
    · intro entry member; cases member

theorem holds : childPlan.Holds model :=
  GeneralNominalHeadLeafPlan189.head_to_plan childPlan rfl rfl model head_equations
    ⟨(packet_models model final_model.1.1.1).1,(packet_models model final_model.1.1.1).2.1⟩

theorem requests_empty (root : GeneralSourceDictionaries.Occurrence roles) : requests finish.core root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := mem_requests_iff.mp member
  rw [raw_sites] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl <;> cases within

theorem ready : EffectsReady finish.core displayChild childPlan :=
  GeneralNominalHeadInitialEffects188.empty_effects_ready (requests_empty _) childPlan

theorem selected : GeneralNominalCenteredHeadWFBoundary.Local registry finish displayChild (.selected 3 []) := by
  refine B4TargetV6.Local.selected GeneralNominalNonleafChild193.safe GeneralNominalNonleafChild193.unique ?_
  intro conflict
  exact conflict.2 ⟨model,final_model,⟨[],GeneralNominalNonleafChild193.unique⟩,childPlan,frame,ready,head_equations,
    GeneralNominalHeadLeafPlan189.output_equations_empty childPlan (requests_empty _) model⟩

theorem alias_identity (related : GeneralNominalSaturationState.Alias finish.core.erased.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem choice : GeneralNominalCycleSteps.ChoiceCompatible finish.core.erased.current childPacket := by
  intro prior member same
  change prior ∈ [packet] at member
  cases List.mem_singleton.mp member
  have bad := alias_identity same
  exact False.elim ((by decide +kernel : displayChild.identity ≠ displayRoot.identity) bad)

theorem support_ready_at (slot : Fin 2) : GeneralNominalSupport.ReadyAt finish.core.erased [] slot.val := by
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero; subst slot
    exact GeneralNominalSupport.source_ready _ _ _ _ _
      (GeneralNominalSupport.Head.nominal (snapshot := GeneralNominalExamples.state true) 0 GeneralNominalExamples.listDescriptor rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl) []
  · have same : slot = 1 := by apply Fin.ext; have bound := slot.isLt; omega
    subst slot
    exact GeneralNominalSupport.source_ready _ _ _ _ _
      (GeneralNominalSupport.Head.scalar (snapshot := GeneralNominalExamples.state true) 1 .int rfl)
      (GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl) []

theorem value_guard : GeneralNominalValueSupport.PacketGuard finish.core.erased childPacket [] := by
  apply (GeneralNominalCenteredHeadStepAvailability.frame_value_iff frame []).mpr
  apply GeneralNominalValueSupport.source_decision
  exact ⟨(by intro _ member; cases member),fun _ => support_ready_at 1,fun _ _ _ _ _ slot _ => support_ready_at slot⟩

theorem installation_model : InstallationModels finish childPlan [] model := by
  refine ⟨final_model,holds,
    GeneralNominalHeadLeafPlan189.output_equations_empty childPlan (requests_empty _) model,?_,?_⟩
  · exact GeneralNominalHeadLeafPlan189.output_equations_empty (state := ⟨GeneralNominalCenteredSteps.install finish.core childPlan [],[]⟩)
      childPlan (GeneralNominalHeadLeafPlan189.installed_requests_empty childPlan rfl (requests_empty _) []) model
  · intro effect member
    change effect ∈ [record enabled] at member
    cases List.mem_singleton.mp member
    exact GeneralNominalHeadLeafPlan189.output_equations_empty (state := ⟨GeneralNominalCenteredSteps.install finish.core childPlan [],[]⟩)
      plan (GeneralNominalHeadLeafPlan189.installed_requests_empty childPlan rfl (requests_empty _) []) model

theorem child_enabled : Installable registry finish childPlan [] := by
  have localOld := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  refine ⟨frame,?_,GeneralNominalNonleafChild193.safe,ready,?_,choice,value_guard,?_,?_,model,installation_model⟩
  · rw [GeneralNominalHeadLeafPlan189.children_empty childPlan rfl]
    exact GeneralNominalNonleafChild193.unique
  · change (GeneralNominalPacketSupport.namedSchema childPlan.packet).unknown = false
    rw [GeneralNominalHeadLeafPlan189.named_schema_empty childPlan rfl rfl]
  · exact GeneralNominalCenteredHeadStepAvailability.selected_safe localOld childPlan frame.center_recorded
      childPlan.input_exact frame.registry_eq frame.context_eq frame.visible frame.role_eq frame.prepared frame.located
  · exact GeneralNominalCenteredHeadStepAvailability.selected_alternatives localOld childPlan.input
      frame.center_recorded childPlan.input_exact

theorem child_build : GeneralNominalReusableForest192.Build registry displayRoot finish [displayChild] [.node 3 []] finish := by
  apply GeneralNominalReusableForest192.Build.reuse childPlan [] child_enabled child_generated committed
  · rw [GeneralNominalHeadLeafPlan189.children_empty childPlan rfl]
    exact .nil _
  · exact .nil _

theorem source_build : GeneralNominalReusableForest192.Build registry displayRoot start [displayRoot] [.node 1 [.node 3 []]] finish := by
  apply GeneralNominalReusableForest192.Build.cons plan [] enabled .root novel
  · rw [children_exact]
    exact child_build
  · exact .nil _

/-- An actual nonleaf WF source certificate: parent installation, generated
terminal-child committed reuse, and same-final-model recursive evidence. -/
theorem source_tree_sound :
    B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry displayRoot finish ∧
    (∃ assignment, Models finish assignment) ∧
    ∀ assignment, Models finish assignment → Models start assignment ∧
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry finish assignment displayRoot (.node 1 [.node 3 []]) :=
  GeneralNominalReusableForest192.source_tree_sound _ initial_source source_build
end Yulang.GeneralNominalNonleafReuse193
