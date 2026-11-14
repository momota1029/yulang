import Yulang.GeneralNominalCenteredClassLocalChoiceTrace
import Yulang.GeneralNominalCenteredClassLocalBoundary

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace Yulang.GeneralNominalCenteredClassLocalChoiceLocal
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps CommonNominalFullCarrier
open GeneralNominalCenteredClassLocalChoiceSource
open GeneralNominalCenteredClassLocalChoiceTrace
open GeneralNominalExamples (context state listDescriptor interpretation state_models)

noncomputable abbrev current := finish.erased.current.context
abbrev focus := child false

private theorem sources_shape (source : Nat) (member : source ∈ GeneralNominalState.sources current.state) :
    source = 0 ∨ source = 1 ∨ source ∈ GeneralNominalAllocation.reserved (state true) registry root.identity := by
  simp only [GeneralNominalState.sources] at member
  change source ∈ (([0,1] ++ [0,1]) ++ GeneralNominalAllocation.reserved (state true) registry root.identity ++ []) ++ _ at member
  rcases List.mem_append.mp member with before | ordinary
  · simp only [List.append_nil] at before
    rcases List.mem_append.mp before with base | allocated
    · simp at base; rcases base with h | h | h | h <;> simp [h]
    · exact Or.inr (Or.inr allocated)
  · have shape : current.state.ordinary.flatMap GeneralNominalState.atomSources = [1,1,0,0,0,0,1,1] := by decide +kernel
    rw [shape] at ordinary
    simp at ordinary
    rcases ordinary with h | h | h <;> simp [h]

theorem fresh (invocation : Nat) : GeneralNominalAllocation.Fresh current.state registry invocation := by
  intro key member collision
  rcases sources_shape _ collision with zero | one | allocated
  · have above := GeneralNominalIdentities.source_above_seed (state true).seed key
    change GeneralNominalIdentities.source (state true).seed key = 0 at zero
    omega
  · have above := GeneralNominalIdentities.source_above_seed (state true).seed key
    change GeneralNominalIdentities.source (state true).seed key = 1 at one
    have seed : (state true).seed = 1 := rfl
    omega
  · obtain ⟨old,owned,equal⟩ := List.mem_map.mp allocated
    have same := (GeneralNominalIdentities.source_identity (state true).seed old key).mp equal
    subst old
    exact List.mem_append_right _ owned

theorem child_query : GeneralNominalInspection.queries current.state current.interpretation childDeclaration = [.scalar .int] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,childDeclaration]
  change GeneralNominalInspection.translate GeneralDeclarationExamples.constructors interpretation (.app 2 []) = _
  simp [GeneralNominalInspection.translate,interpretation]

theorem child_report : report current childDeclaration [((1 : Fin 2),(1 : Fin 2))] =
    { inspected := [((1 : Fin 2),(1 : Fin 2))], checked := [((1 : Fin 2),(1 : Fin 2)),((1 : Fin 2),(1 : Fin 2))] } := by
  simp [report,child_query,inspectMany,inspect,Report.visit,Report.append,
    show current.state.nominals (1 : Fin 2) = none from rfl,
    show current.state.view.heads (1 : Fin 2) = .scalar .int from rfl]

theorem canonical_child : GeneralCanonicalChildOrder.canonicalDeclaration childDeclaration = childDeclaration := by
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,childDeclaration]

theorem child_schema : generated registry current focus childDeclaration child_checked [((1 : Fin 2),(1 : Fin 2))] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_child]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_zero,GeneralNominalMaterialization.generated,
    focus,child,childDeclaration,leaf,roles]

theorem child_branch (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models current.state m) :
    BranchModels registry current focus childDeclaration child_checked [((1 : Fin 2),(1 : Fin 2))] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [child_report]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.Compatible]
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.merges,childDeclaration,
        Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [child_report]; simp [ProjectionModels]
  · rw [child_schema]; exact GeneralNominalMaterialization.empty_models ..

theorem child_prepared : Prepared registry current focus childDeclaration child_checked := by
  refine ⟨metadata,?_,fresh _,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,exampleModel,child_branch exampleModel finish_model.1.1⟩
  · constructor
    · intro index
      have member : 1 ∈ GeneralNominalState.sources current.state :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩))))
      exact ⟨member,member⟩
    · intro output member; cases member
  · rw [child_report]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ impossible; cases impossible),?_⟩; rw [child_schema]

noncomputable abbrev descendants := GeneralNominalAllocation.children current.state registry focus childDeclaration child_checked []

theorem descendants_nonempty : descendants ≠ [] := by
  have count := GeneralCanonicalChildOrder.canonicalEmit_perm focus.identity childDeclaration child_checked
    (GeneralNominalAllocation.capture current.state registry focus.identity childDeclaration.id [])
    (GeneralNominalAllocation.allocation current.state registry focus.identity childDeclaration.id)
  intro empty
  have size := congrArg List.length empty
  change (List.map _ (GeneralCanonicalChildOrder.canonicalEmit _ _ _ _ _)).length = 0 at size
  simp only [List.length_map,GeneralNominalAllocation.frame] at size
  rw [← count.length_eq,GeneralDeclarationDemands.emitAll_length] at size
  cases size

theorem child_known : ¬ GeneralNominalState.RootPending current.state focus.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

theorem child_survivor : Survivor registry current focus 2 descendants := by
  refine ⟨child_known,childDeclaration,by simp,child_checked,rfl,rfl,[((1 : Fin 2),(1 : Fin 2))],rfl,child_prepared,?_⟩
  rw [child_report]; rfl

private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (exampleModel source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem feedback_acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle finish.erased.current source :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ exampleModel finish_model.1 height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

theorem raw_acyclic (slot : Fin current.state.base.slots) : ¬ GeneralNominalCycleK2.Cycle current.state slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge current.state first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument exampleModel (finish_model.1.1)
      exact GeneralNominalOutputGrowthModels.observation_decreases exampleModel height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path current.state first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_raw_recurs (slot : Fin current.state.base.slots) : ¬ GeneralNominalCycleK2.RecursAt current.state slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle


theorem canonical_good : GeneralCanonicalChildOrder.canonicalDeclaration goodDeclaration = goodDeclaration := by
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,goodDeclaration]

theorem good_schema : generated registry current focus goodDeclaration good_checked [((1 : Fin 2),(1 : Fin 2))] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_good]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_zero,GeneralNominalMaterialization.generated,
    focus,child,goodDeclaration,leaf,roles]

theorem good_branch (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models current.state m) :
    BranchModels registry current focus goodDeclaration good_checked [((1 : Fin 2),(1 : Fin 2))] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [show report current goodDeclaration _ = report current childDeclaration _ from rfl,child_report]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.Compatible]
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.merges,goodDeclaration,
        Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [show report current goodDeclaration _ = report current childDeclaration _ from rfl,child_report]; simp [ProjectionModels]
  · rw [good_schema]; exact GeneralNominalMaterialization.empty_models ..

theorem good_prepared : Prepared registry current focus goodDeclaration good_checked := by
  refine ⟨metadata,?_,fresh _,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,exampleModel,good_branch exampleModel finish_model.1.1⟩
  · constructor
    · intro index
      have member : 1 ∈ GeneralNominalState.sources current.state :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩))))
      exact ⟨member,member⟩
    · intro output member; cases member
  · rw [show report current goodDeclaration _ = report current childDeclaration _ from rfl,child_report]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ impossible; cases impossible),?_⟩; rw [good_schema]



noncomputable abbrev goodChildren := GeneralNominalAllocation.children current.state registry focus goodDeclaration good_checked []

theorem good_survivor : Survivor registry current focus 3 goodChildren := by
  refine ⟨child_known,goodDeclaration,by simp,good_checked,rfl,rfl,[((1 : Fin 2),(1 : Fin 2))],rfl,good_prepared,?_⟩
  change goodChildren = GeneralNominalAllocation.children _ _ _ _ _ (GeneralNominalRecursiveInspection.bindings _ (report current childDeclaration _))
  rw [child_report]; rfl

theorem raw_safe : GeneralNominalLocalBoundary.SafeKnown (GeneralNominalFeedbackK2.fields roles) registry finish.erased.current focus := by
  refine ⟨child_known,?_,?_,?_⟩
  · rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
    · exact no_raw_recurs slot cycle
    · exact feedback_acyclic _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
    · exact no_raw_recurs visited.1 cycle
    · exact feedback_acyclic _ cycle
  · rintro (⟨_,d,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl | rfl
      · cases role
      · exact notPrepared child_prepared
      · exact notPrepared good_prepared
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
private theorem graph_tests : (graph finish).tests = [(.source 0,.nominal 0 1),(.source output,.scalar .int)] := by
  change GeneralNominalCenteredSteps.Plan.tests plan ++ [] = _
  rw [List.append_nil]
  unfold GeneralNominalCenteredSteps.Plan.tests
  rw [head_schema,named_schema]
  simp [GeneralNominalCenters.Plan.schema,GeneralNominalCenters.Plan.childRequests,
    List.ofFn_succ,GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,normalize]

private theorem center_distinct : ¬ GeneralNominalOriginTerms.Same exampleModel (.source 0) (.source 1) := by
  intro same
  have equal := same.2.2 _ _ (.source 0) (.source 1)
  have impossible : 1 = 0 := (GeneralNominalOutputGrowth.tower_equivalent 1 0).mp equal
  cases impossible

private theorem recorded_shapes (recorded : GeneralNominalCenteredGraph.Recorded (graph finish) first last) :
    GeneralNominalOriginTerms.Same exampleModel first (.source 0) ∧
    GeneralNominalOriginTerms.Same exampleModel last (.source 1) := by
  cases recorded with
  | structural shape index member => simp [graph_tests] at member
  | nominal name arity index member =>
    simp only [graph_tests,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with ⟨rfl,same⟩ | ⟨rfl,same⟩
    · cases same
      have zero : index.val = 0 := by omega
      rw [zero]
      refine ⟨GeneralNominalOriginTerms.source_self exampleModel 0,?_⟩
      have eqs := finish_model.2.2 plan (List.mem_singleton_self _)
      have actual := eqs.2.2.1.2
      rw [head_schema] at actual
      have same := actual ⟨0,origin,.actual⟩ (List.mem_singleton_self _)
      simpa only [ite_true,binder_zero] using same
    · cases same

private theorem graph_acyclic (origin : Origin) : ¬ GeneralNominalCenteredGraph.Cyclic (graph finish) origin := by
  have endpoints {first last} (edge : GeneralNominalCenteredGraph.Edge (graph finish) first last) :
      GeneralNominalOriginTerms.Same exampleModel first (.source 0) ∧
      GeneralNominalOriginTerms.Same exampleModel last (.source 1) := by
    obtain ⟨parent,child,recorded,left,right⟩ := edge
    have shape := recorded_shapes recorded
    exact ⟨GeneralNominalOriginTerms.same_trans (left exampleModel finish_model) shape.1,
      GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm (right exampleModel finish_model)) shape.2⟩
  rintro ⟨⟨next,edge,path⟩,_⟩
  have one := endpoints edge
  cases path with
  | nil => exact center_distinct (GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm one.1) one.2)
  | cons edge rest =>
    have two := endpoints edge
    exact center_distinct (GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm two.1) one.2)

theorem centered_acyclic (origin : Origin) : ¬ Cyclic finish origin := by
  rintro (⟨source,_,cycle,_⟩ | cycle)
  · exact feedback_acyclic source cycle
  · exact graph_acyclic origin cycle

theorem child_decision : DecisionGuard registry finish focus := by
  have ready (slot : Fin 2) : GeneralNominalSharedSupport.ReadyAt finish.erased slot.val := by
    by_cases zero : slot.val = 0
    · have same : slot = 0 := Fin.ext zero; subst slot
      exact ⟨_,_,GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) listDescriptor rfl,
        GeneralNominalSharedSupport.source_head _ (GeneralNominalSupport.Head.nominal (snapshot := state true) 0 listDescriptor rfl)⟩
    · have same : slot = 1 := by apply Fin.ext; have bound := slot.isLt; omega
      subst slot
      exact ⟨_,_,GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl,
        GeneralNominalSharedSupport.source_head _ (GeneralNominalSupport.Head.scalar (snapshot := state true) 1 .int rfl)⟩
  exact GeneralNominalCenteredSupport.legacy_decision ⟨fun _ => ready 1,fun _ _ _ _ _ slot _ => ready slot⟩

theorem child_alias (first last : Bool) : GeneralNominalSaturationState.Alias finish.erased.current
    (child first).identity (child last).identity := by
  cases first <;> cases last
  · exact .refl _
  · exact .symm (.edge (List.mem_cons_self ..))
  · exact .edge (List.mem_cons_self ..)
  · exact .refl _

theorem ready : GeneralNominalCenteredAdministrativeLocal.AdministrativeReady finish focus := by
  refine ⟨⟨centerSite false,?_,rfl⟩,?_,?_⟩
  · change centerSite false ∈ before.sites
    rw [center_sites]; simp
  · intro first present same last recorded inputs
    change first ∈ before.erased.current.sites at present
    change last ∈ before.erased.current.sites at recorded
    rw [raw_sites] at present recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present recorded
    rcases present with rfl | rfl | rfl
    · have impossible := congrArg (fun x : Occurrence roles => x.demand.role) same
      cases impossible
    all_goals
      rcases recorded with rfl | rfl | rfl
      · have impossible := inputs.1; cases impossible
      · exact child_alias _ _
      · exact child_alias _ _
  · intro first present same last recorded inputs
    change first ∈ before.sites at present
    change last ∈ before.sites at recorded
    rw [center_sites] at present recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present recorded
    rcases present with rfl | rfl | rfl
    · have impossible := congrArg (fun x : Occurrence roles => x.demand.role) same
      cases impossible
    all_goals
      rcases recorded with rfl | rfl | rfl
      · have impossible := inputs.1; cases impossible
      · exact child_alias _ _
      · exact child_alias _ _

theorem class_safe : GeneralNominalLocalBoundary.SafeKnown
    (GeneralNominalCenteredClassLocalBoundary.fields roles) registry finish focus := by
  refine ⟨raw_safe.1,?_,?_,?_⟩
  · rintro (old | ⟨site,_,_,index,cycle⟩)
    · exact raw_safe.2.1 old
    · exact centered_acyclic _ cycle
  · rintro (old | ⟨other,_,_,_,_,_,_,_,_,entry,_,cycle⟩)
    · exact raw_safe.2.2.1 old
    · exact centered_acyclic _ cycle
  · rintro ((old | missing) | missing)
    · exact raw_safe.2.2.2 old
    · exact missing child_decision
    · exact missing ready

theorem raw_ambiguous : GeneralNominalFeedbackK2.Local registry finish.erased.current focus .ambiguous :=
  .ambiguous raw_safe child_survivor good_survivor (by decide +kernel)

end Yulang.GeneralNominalCenteredClassLocalChoiceLocal
