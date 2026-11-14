import Yulang.GeneralNominalCenteredClassLocalChoiceObstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

/-! The surviving class candidate has value support and a common centered
model. The old occurrence-level uniqueness guard is the remaining obstacle. -/
namespace Yulang.GeneralNominalCenteredClassLocalChoiceFeasibility
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps CommonNominalFullCarrier
open GeneralNominalCenteredClassLocalChoiceSource GeneralNominalCenteredClassLocalChoiceTrace
open GeneralNominalCenteredClassLocalChoiceLocal GeneralNominalCenteredClassLocalChoiceObstruction
open GeneralNominalExamples (state interpretation)

noncomputable def candidate : Plan roles :=
  ⟨⟨registry,current,rawSite false,goodDeclaration,good_checked,[((1 : Fin 2),(1 : Fin 2))]⟩,centerSite false,rfl⟩

theorem frame : GeneralNominalCenteredSelectedCompletion.Frame registry finish focus 3 goodChildren candidate := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,by simp [candidate],rfl,rfl,good_prepared⟩
  · change GeneralNominalAllocation.children current.state registry focus goodDeclaration good_checked
      (GeneralNominalRecursiveInspection.bindings current.state (report current goodDeclaration [((1 : Fin 2),(1 : Fin 2))])) = goodChildren
    rw [show report current goodDeclaration _ = report current childDeclaration _ from rfl,child_report]
    rfl
  · change rawSite false ∈ before.erased.current.sites
    rw [raw_sites]; simp
  · change centerSite false ∈ before.sites
    rw [center_sites]; simp

theorem queries : GeneralNominalInspection.queries current.state current.interpretation goodDeclaration = [.scalar .int] :=
  child_query

theorem head_schema : candidate.headSchema = { tests := [(.source 1,.scalar .int)] } := by
  unfold Plan.headSchema
  rw [show candidate.packet.context = current from rfl,show candidate.packet.declaration = goodDeclaration from rfl,queries]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,candidate,centerSite,child,roles,
    List.ofFn_succ,GeneralDeclarationExamples.bareRole]

theorem input_schema : GeneralNominalPacketSupport.inputSchema candidate.packet = {} := by
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  unfold GeneralCanonicalChildOrder.canonicalEmit
  simp only [show candidate.packet.declaration = goodDeclaration from rfl,canonical_good]
  simp [candidate,goodDeclaration,leaf,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalPacketSupport.inputRequests,GeneralNominalMaterialization.inputRequests,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.Schema.append,
    GeneralNominalAllocation.frame,GeneralDeclarationDemands.childDemand]

theorem named_schema : GeneralNominalPacketSupport.namedSchema candidate.packet = {} := by
  change generated registry current focus goodDeclaration good_checked _ = _
  exact good_schema

theorem equations : candidate.Equations exampleModel := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro index; exact ⟨subtype_refl _,subtype_refl _⟩
  · intro name used
    rcases used with used | ⟨clause,member,used⟩
    · simp [candidate,goodDeclaration,Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at used
    · cases List.mem_singleton.mp member
      cases used
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      exact ⟨⟨_,.source 1⟩,by intro value seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
    · intro entry member; cases member
  · rw [input_schema]
    simp [Plan.SchemaHolds,Plan.schema,GeneralNominalMaterialization.generated]
  · rw [named_schema]
    simp [Plan.SchemaHolds,Plan.schema,GeneralNominalMaterialization.generated]
  · intro clause member signature
    cases List.mem_singleton.mp member
    constructor
    · intro index; exact Fin.elim0 index
    · change candidate.SchemaHolds (candidate.schema []) exampleModel
      simp [Plan.SchemaHolds,Plan.schema,GeneralNominalMaterialization.generated]

theorem raw_decision : GeneralNominalValueSupport.DecisionGuard registry finish.erased focus [] := by
  have ready (slot : Fin 2) : GeneralNominalSupport.ReadyAt finish.erased [] slot.val := by
    by_cases zero : slot.val = 0
    · have same : slot = 0 := Fin.ext zero; subst slot
      exact GeneralNominalSupport.source_ready _ _ _ _ _
        (GeneralNominalSupport.Head.nominal (snapshot := state true) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl)
        (GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl) []
    · have same : slot = 1 := by apply Fin.ext; have bound := slot.isLt; omega
      subst slot
      exact GeneralNominalSupport.source_ready _ _ _ _ _
        (GeneralNominalSupport.Head.scalar (snapshot := state true) (1 : Fin 2) .int rfl)
        (GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl) []
  exact ⟨⟨(by intro _ h; cases h),fun _ => ready 1,fun _ _ _ _ _ slot _ => ready slot⟩,
    GeneralNominalValueSupport.empty_supported _ _⟩

theorem feasible : GeneralNominalCenteredClassLocalProduction.Feasible registry finish candidate :=
  ⟨[],(GeneralNominalCenteredCompletionParts.frame_value_iff frame []).mpr raw_decision,
    exampleModel,finish_model,good_branch exampleModel finish_model.1.1,equations⟩

theorem not_raw_unique : ¬ GeneralNominalCenteredClassLocalBoundary.RawUnique registry finish focus 3 := by
  intro unique
  have impossible : 2 = 3 := unique 2 descendants child_survivor
  cases impossible

theorem not_committed : ¬ GeneralNominalFeedbackSteps.Committed finish.erased.current candidate.packet := by
  intro committed
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil goodChildren good_children_nonempty
  have edge := committed.2 child (frame.children_eq ▸ member)
  change (focus,child) ∈ [] ++ children.map (fun c => (root,c)) at edge
  have edge' : (focus,child) ∈ children.map (fun c => (root,c)) := by simpa only [List.nil_append] using edge
  obtain ⟨_,_,same⟩ := List.mem_map.mp edge'
  exact child_not_root false (congrArg (fun pair => pair.1.identity) same).symm

theorem joint_and_feasible_but_blocked :
    GeneralNominalJointCandidates.Joint registry finish.erased.current focus 3 ∧
    GeneralNominalCenteredClassLocalProduction.Feasible registry finish candidate ∧
    ¬ GeneralNominalCenteredBoundary.Installable registry finish candidate :=
  ⟨good_joint,feasible,not_installable candidate rfl⟩

end Yulang.GeneralNominalCenteredClassLocalChoiceFeasibility
