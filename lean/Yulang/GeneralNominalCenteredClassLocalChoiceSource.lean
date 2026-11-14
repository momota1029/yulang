import Yulang.GeneralNominalCenteredPermutationSimulation
import Yulang.GeneralNominalCenteredPointMergeExample
import Yulang.GeneralDictionarySelectedAliasConflict

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A parent emits two same-input demands, with an output request on only one
occurrence. The child implementation has a different associated output. -/
namespace Yulang.GeneralNominalCenteredClassLocalChoiceSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps
open CommonNominalFullCarrier
open GeneralNominalExamples (context state interpretation listDescriptor state_models)
abbrev exampleModel := GeneralNominalExamples.model
open GeneralDeclarationExamples (constructors)

abbrev roles : Roles.RoleDecls := fun role =>
  if role = 2 then ⟨0,fun _ => none,by intros; contradiction⟩
  else if role = 1 then GeneralDeclarationExamples.outputRole 0 else GeneralDeclarationExamples.bareRole
abbrev requested : Clause := ⟨10,1,[.var 0],[⟨30,0,.app 2 []⟩]⟩
abbrev plain : Clause := ⟨11,1,[.var 0],[]⟩
abbrev parent : Declaration := ⟨1,0,[.app 0 [.var 0]],[requested,plain],[],[]⟩
abbrev leaf : Clause := ⟨20,2,[],[]⟩
abbrev childDeclaration : Declaration := ⟨2,1,[.app 2 []],[leaf],[⟨40,0,.app 0 [.app 2 []]⟩],[]⟩
abbrev goodDeclaration : Declaration := ⟨3,1,[.app 2 []],[leaf],[⟨40,0,.app 2 []⟩],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[parent,childDeclaration,goodDeclaration]⟩
abbrev root : Occurrence roles := ⟨100,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩

theorem parent_checked : DeclarationChecked constructors roles parent := by
  constructor
  · refine ⟨rfl,by simp,?_,?_⟩
    · intro name body impossible; cases impossible
    · intro clause member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · refine ⟨rfl,?_⟩
        intro equation member
        cases List.mem_singleton.mp member
        exact ⟨none,rfl⟩
      · exact ⟨rfl,by intro _ h; cases h⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> (unfold ConservativeSmaller; decide +kernel)
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact unary_descent 0 0

theorem child_checked : DeclarationChecked constructors roles childDeclaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
    · intro name body member
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨_,List.mem_singleton_self _,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at member
    · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,by intro _ h; cases h⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member; exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member; unfold ConservativeSmaller; decide +kernel
  · intro clause member; cases List.mem_singleton.mp member
    intro capture
    change Smaller [.app 2 []] []
    exact (checkSmaller_exact _ _).mp (by decide +kernel)

theorem good_checked : DeclarationChecked constructors roles goodDeclaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
    · intro name body member
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨_,List.mem_singleton_self _,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at member
    · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,by intro _ h; cases h⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member; exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member; unfold ConservativeSmaller; decide +kernel
  · intro clause member; cases List.mem_singleton.mp member
    intro capture
    change Smaller [.app 2 []] []
    exact (checkSmaller_exact _ _).mp (by decide +kernel)

theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact parent_checked
  · exact child_checked
  · exact good_checked

theorem metadata : Metadata registry (context true) :=
  GeneralDictionarySupportRecursiveExample.initial_source.metadata

theorem source : GeneralNominalSourceFormation.InitialSource registry (context true) root where
  roles_agree := rfl
  metadata := metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  intervals := fun _ _ _ => subtype_refl _
  below_seed := GeneralDictionarySupportRecursiveExample.initial_source.below_seed
  unallocated := rfl

theorem query : GeneralNominalInspection.queries (state true) interpretation parent = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,interpretation]

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context true,GeneralNominalDemandMerging.pointSite root,parent,parent_checked,[(0,0)]⟩
abbrev start := initial (context true) root
abbrev plan : Plan roles := ⟨packet,rootSite (state true).seed root,rfl⟩
abbrev output : Nat := GeneralNominalAllocation.source (state true) registry 100 (100,1,5,30,0)
abbrev child (requested : Bool) : Occurrence roles :=
  ⟨GeneralNominalAllocation.source (state true) registry 100 (100,1,6,(if requested then 10 else 11),0),
    ⟨1,fun _ => (1,1),if requested then [⟨0,output⟩] else [],by
      intro entry member
      split at member
      · cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
      · cases member⟩⟩

theorem raw_report : GeneralNominalPacketSupport.report packet =
    GeneralNominalUnaryCaptureFacts.captured (state true) 0 0 0 (1,1) :=
  GeneralNominalUnaryCaptureFacts.report_exact (context true) parent 0 listDescriptor rfl 0 (1,1) rfl query

theorem bindings : packet.bindings = [(0,(1,1))] := by
  change GeneralNominalRecursiveInspection.bindings _ (GeneralNominalPacketSupport.report packet) = _
  rw [raw_report]; rfl

theorem canonical_parent : GeneralCanonicalChildOrder.canonicalDeclaration parent = parent := by
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    parent,List.mergeSort_pair,requested,plain]

theorem named_schema : GeneralNominalPacketSupport.namedSchema packet =
    { tests := [(.source output,.scalar .int)] } := by
  unfold GeneralNominalPacketSupport.namedSchema generated GeneralNominalMaterialization.requests
  rw [show GeneralNominalRecursiveInspection.bindings _ _ = packet.bindings from rfl,bindings]
  unfold GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration packet.declaration = parent from canonical_parent]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    List.ofFn_succ,GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,interpretation,
    normalize,normalizeArgs,GeneralNominalAllocation.frame,GeneralNominalAllocation.allocation,GeneralNominalAllocation.origin,output,
    packet,root,parent,requested,plain,GeneralNominalDemandMerging.pointSite,GeneralDeclarationDemands.outputTarget]

theorem input_schema : GeneralNominalPacketSupport.inputSchema packet = {} := by
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  unfold GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration packet.declaration = parent from canonical_parent]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralNominalMaterialization.inputRequests,
    List.ofFn_succ,normalize,GeneralNominalMaterialization.generated]

theorem branch (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m)
    (out : Equivalent (m output).1 (.base .int)) : packet.Holds m := by
  have privateModel := GeneralNominalUnaryCaptureFacts.private_models (context true) registry root parent 0 listDescriptor rfl 0 rfl (1,1) rfl query m valid
  refine ⟨privateModel.1,privateModel.2,?_⟩
  change GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema packet) m
  rw [named_schema]
  refine ⟨?_,by simp,by simp,by simp⟩
  intro entry member; cases List.mem_singleton.mp member
  exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact out⟩

theorem output_nonzero : output ≠ 0 := by
  have above := GeneralNominalIdentities.source_above_seed (state true).seed (100,1,5,30,0)
  intro equal
  change output > _ at above
  rw [equal] at above
  omega

theorem branch_model : packet.Holds exampleModel :=
  branch exampleModel (state_models true) (by simp only [exampleModel,GeneralNominalExamples.model,output_nonzero,ite_false]; exact ⟨subtype_refl _,subtype_refl _⟩)

noncomputable abbrev children := packet.children

theorem children_exact : children = [child true,child false] := by
  change GeneralNominalAllocation.children _ _ _ _ _ packet.bindings = _
  rw [bindings]
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration packet.declaration = parent from canonical_parent]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    normalize,child,Declaration.outputNames,GeneralNominalAllocation.allocation,
    packet,GeneralNominalDemandMerging.pointSite,root,parent,requested,plain,GeneralNominalAllocation.origin,output]

theorem prepared : Prepared registry (context true) root parent parent_checked := by
  refine ⟨metadata,source.linked,GeneralNominalUnaryCaptureFacts.initial_fresh _ _ _ (by decide +kernel),[(0,0)],rfl,?_,?_,exampleModel,branch_model⟩
  · change Finished (GeneralNominalPacketSupport.report packet)
    rw [raw_report]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ h; cases h),?_⟩
    change (GeneralNominalPacketSupport.namedSchema packet).unknown = false
    rw [named_schema]

theorem no_pending : ¬ GeneralNominalState.RootPending (state true) root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨listDescriptor,rfl⟩⟩

theorem survivor : Survivor registry (context true) root 1 children :=
  ⟨no_pending,parent,by simp, parent_checked,rfl,rfl,[(0,0)],rfl,prepared,rfl⟩

private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (exampleModel source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem raw_acyclic (slot : Fin (state true).base.slots) : ¬ GeneralNominalCycleK2.Cycle (state true) slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge (state true) first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument exampleModel (state_models true)
      exact GeneralNominalOutputGrowthModels.observation_decreases exampleModel height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path (state true) first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_raw_recurs (slot : Fin (state true).base.slots) : ¬ GeneralNominalCycleK2.RecursAt (state true) slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

theorem initial_feedback_acyclic (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.erased.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ exampleModel
    ((GeneralNominalSaturationState.initial_models ..).mpr (state_models true))
    height model_height (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem selected : GeneralNominalFeedbackK2.Local registry start.erased.current root (.selected 1 children) := by
  refine .selected ⟨no_pending,?_,?_,?_⟩ ⟨survivor,?_⟩
  · rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
    · exact no_raw_recurs slot cycle
    · exact initial_feedback_acyclic _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
    · exact no_raw_recurs visited.1 cycle
    · exact initial_feedback_acyclic _ cycle
  · rintro (⟨_,d,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl | rfl
      · exact notPrepared prepared
      · cases role
      · cases role
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
  · intro key cs found
    have original := found
    obtain ⟨_,d,visible,check,identity,role,_⟩ := found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · have equal : key = 1 := identity.symm; subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked (context true) root 1 cs children original survivor⟩
    · cases role
    · cases role

theorem source_decisions : GeneralNominalSupport.DecisionGuard start.erased registry root [] := by
  have ready (slot : Fin 2) : GeneralNominalSupport.ReadyAt start.erased [] slot.val := by
    by_cases zero : slot.val = 0
    · have equal : slot = 0 := Fin.ext zero; subst slot
      exact GeneralNominalSupport.source_ready start.erased 0 (.nominal 0 1) _ _
        (GeneralNominalSupport.Head.nominal (snapshot := state true) 0 listDescriptor rfl)
        (GeneralNominalSupport.Head.nominal (snapshot := state true) 0 listDescriptor rfl) []
    · have equal : slot = 1 := by apply Fin.ext; have bound := slot.isLt; omega
      subst slot
      exact GeneralNominalSupport.source_ready start.erased 1 (.scalar .int) _ _
        (GeneralNominalSupport.Head.scalar (snapshot := state true) 1 .int rfl)
        (GeneralNominalSupport.Head.scalar (snapshot := state true) 1 .int rfl) []
  exact ⟨(by intro _ h; cases h),fun _ => ready 0,fun _ _ _ _ _ slot _ => ready slot⟩

theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.erased.current packet := by
  refine ⟨⟨rfl,rfl,List.mem_singleton_self _,by simp,rfl,rfl,prepared,
    GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,?_,?_⟩,selected,?_⟩
  · intro prior member; cases member
  · intro other member _; cases List.mem_singleton.mp member; exact .refl _
  · exact ⟨exampleModel,(GeneralNominalSaturationState.initial_models ..).mpr (state_models true),branch_model⟩
  · exact GeneralNominalJointCandidates.initial_joint registry (context true) root parent
      (by simp) parent_checked rfl [(0,0)] rfl prepared exampleModel branch_model
  · intro other member _; cases List.mem_singleton.mp member; exact .refl _

theorem raw_guard : GeneralNominalSupportSteps.PacketGuard start.erased packet [] :=
  ⟨⟨source_decisions.1,source_decisions.2.1,source_decisions.2.2 parent (by simp) rfl _ rfl⟩,source_decisions⟩

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.erased.current packet := by
  intro committed
  have absent := committed.2 (child true) (by change child true ∈ children; rw [children_exact]; simp)
  cases absent

end Yulang.GeneralNominalCenteredClassLocalChoiceSource
