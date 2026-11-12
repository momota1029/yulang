import Yulang.GeneralDictionaryJointMergeExample
import Yulang.GeneralDictionaryEarlyMergeBoundary
import Yulang.GeneralDictionarySupportRecursiveExample

/-! Reachable nonempty associated-output merge with current source evidence.
The registry contains the checked parent and a terminal scalar-output child
implementation. The actual Initial→parent install→child merge path, common model,
both child branches, Joint and complete terminal dictionaries coexist below.
The two child classes remain uncommitted. No Stable or general V5 result follows.
Unlike the sibling OutputMergeReachable fixture, terminal7 is present here. -/
namespace Yulang.GeneralDictionaryOutputMergeSuccess
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation)

abbrev firstClause : Clause := ⟨10,1,[.var 0],[⟨30,0,.app 2 []⟩]⟩
abbrev secondClause : Clause := ⟨11,1,[.var 0],[⟨31,0,.app 2 []⟩]⟩
abbrev declaration : Declaration := { GeneralDeclarationExamples.display with
  requirements := [firstClause, secondClause] }
abbrev terminal := GeneralDictionaryJointMergeExample.terminal
abbrev terminal_checked := GeneralDictionaryJointMergeExample.terminal_checked
abbrev registry : Registry := ⟨constructors, roles, [declaration,terminal]⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,by simp,?_,?_⟩
    · intro name body impossible; cases impossible
    · intro clause member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals
        refine ⟨rfl,?_⟩
        intro equation member
        have eq := List.mem_singleton.mp member; subst equation
        exact ⟨none,rfl⟩
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize, variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> (unfold ConservativeSmaller; decide +kernel)
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact unary_descent 0 0

theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro d member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact checked
  · exact terminal_checked

abbrev start (root : Occurrence roles) : Tracked roles := GeneralNominalSupport.initial (context true) root
private theorem all_heads (slot : Fin (state true).base.slots) :
    ∃ test observation, Head (state true) ((state true).base.source slot) test observation := by
  have bounded := slot.isLt
  change slot.val < 2 at bounded
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by
      apply Fin.ext
      change slot.val = 1
      omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl⟩

private theorem roots (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    Roots (start root) [] root := by
  intro index
  rw [show (root.demand.arguments index).1 = 0 by rw [arguments index]]
  exact source_ready (start root) 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := state true) 0 listDescriptor rfl) (Head.nominal (snapshot := state true) 0 listDescriptor rfl) []

theorem all_source_decisions (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    DecisionGuard (start root) registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),roots root arguments,?_⟩
  intro declaration visible role bounds located slot member
  obtain ⟨test,observation,head⟩ := all_heads slot
  exact source_ready (start root) _ test observation observation head head []

private def height (source : Nat) : Nat := if source = 0 then 1 else 0

private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

private theorem raw_acyclic (slot : Fin (state true).base.slots) : ¬ GeneralNominalCycleK2.Cycle (state true) slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge (state true) first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model (state_models true)
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path (state true) first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

private theorem no_raw_recurs (slot : Fin (state true).base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt (state true) slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

private theorem no_feedback_cycle (root : Occurrence roles) (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle (start root).current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model ((initial_models ..).mpr (state_models true))
    height model_height (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

private theorem no_root (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.RootK2 (start root).current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact no_feedback_cycle root _ cycle

private theorem no_candidate (root : Occurrence roles) :
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry (start root).current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact no_feedback_cycle root _ cycle


theorem query : GeneralNominalInspection.queries (state true) interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]

abbrev outputTarget (n : Nat) : Nat :=
  GeneralNominalAllocation.source (state true) registry 100
    (GeneralNominalAllocation.origin 100 1 5 (n+20) 0)

theorem output_nonzero (n : Nat) : outputTarget n ≠ 0 := by
  have positive := GeneralNominalIdentities.source_above_seed (state true).seed
    (GeneralNominalAllocation.origin 100 1 5 (n+20) 0)
  unfold outputTarget GeneralNominalAllocation.source
  omega

theorem schema : generated registry (context true) displayRoot declaration checked [(0,0)] =
    {tests := [(.source (outputTarget 10),.scalar .int),(.source (outputTarget 11),.scalar .int)]} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair])]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,normalizeArgs,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,interpretation,outputTarget,GeneralNominalAllocation.allocation,
    GeneralDeclarationDemands.outputTarget,Declaration.outputNames]

theorem branch : BranchModels registry (context true) displayRoot declaration checked [(0,0)] model := by
  have privateModel := private_models (context true) registry displayRoot declaration 0 listDescriptor rfl 0 rfl
    (1,1) rfl query model (state_models true)
  refine ⟨privateModel.1,privateModel.2,?_⟩
  rw [schema]
  refine ⟨?_,by simp,by simp,by simp⟩
  intro test member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    simp only [Test.Holds,output_nonzero]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem prepared : Prepared registry (context true) displayRoot declaration checked := by
  refine ⟨GeneralDictionarySupportRecursiveExample.initial_source.metadata,
    GeneralDictionarySupportRecursiveExample.initial_source.linked,
    initial_fresh _ _ _ (by decide +kernel),[(0,0)],rfl,?_,?_,model,branch⟩
  · rw [report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query]
    exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ h; cases h),?_⟩; rw [schema]

noncomputable abbrev children := GeneralNominalAllocation.children (state true) registry displayRoot declaration checked
    (bindings (state true) (report (context true) declaration [(0,0)]))

theorem survivor : Survivor registry (context true) displayRoot 1 children :=
  ⟨GeneralNominalRecursiveExamples.display_survivor.1,declaration,by simp,checked,rfl,rfl,[(0,0)],rfl,prepared,rfl⟩

theorem selected : GeneralNominalSupportBoundary.Local registry (start displayRoot) displayRoot (.selected 1 children) := by
  apply GeneralNominalSupportBoundary.selected_supported (support := []) _ (all_source_decisions displayRoot (fun _ => rfl))
  refine .selected ⟨survivor.1,no_root _,no_candidate _,?_⟩ ⟨survivor,?_⟩
  · rintro (⟨_,d,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · exact notPrepared prepared
      · contradiction
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
  · intro key cs found
    have original := found
    obtain ⟨_,d,visible,check,identity,role,_⟩ := found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · have equal : key = 1 := identity.symm; subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked (context true) displayRoot 1 cs children original survivor⟩
    · contradiction

abbrev child (clause : Nat) : Occurrence roles :=
  ⟨GeneralNominalAllocation.source (state true) registry 100
    (GeneralNominalAllocation.origin 100 1 6 clause 0),
    ⟨1,fun _ => (1,1),[⟨0,outputTarget clause⟩],by
      intro output member
      have eq := List.mem_singleton.mp member; subst output
      exact ⟨none,rfl⟩⟩⟩

theorem children_exact : children = [child 10,child 11] := by
  unfold children
  rw [report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query]
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from
    (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair])]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    normalize,child,Declaration.outputNames,bindings,captured,GeneralNominalAllocation.allocation,outputTarget]

abbrev packet : Packet roles := ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,declaration,checked,[(0,0)]⟩
noncomputable abbrev before := GeneralNominalSupportSteps.install (start displayRoot) packet []

theorem enabled : GeneralNominalFeedbackSteps.Installable registry (start displayRoot).current packet := by
  have localRule := GeneralNominalSupportBoundary.selected_old selected
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],by simp,rfl,rfl,prepared,
    GeneralNominalFeedbackK2.selected_legacy localRule,?_,?_,?_,?_⟩,localRule,?_⟩
  · intro prior member; cases member
  · intro other member _; have eq := List.mem_singleton.mp member; subst other; exact .refl _
  · exact ⟨model,(initial_models ..).mpr (state_models true),branch⟩
  · exact GeneralNominalJointCandidates.initial_joint registry (context true) displayRoot declaration
      (by simp) checked rfl [(0,0)] rfl prepared model (branch)
  · intro other member _; have eq := List.mem_singleton.mp member; subst other; exact .refl _

theorem packet_guard : PacketGuard (start displayRoot) packet [] := by
  have decisions := all_source_decisions displayRoot (fun _ => rfl)
  exact ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (by simp) rfl _ rfl⟩,decisions⟩

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed (start displayRoot).current packet := by
  intro committed
  have absent := committed.2 (child 10) (by change child 10 ∈ children; rw [children_exact]; simp)
  cases absent

theorem source : GeneralNominalSourceFormation.InitialSource registry (context true) displayRoot where
  roles_agree := rfl
  metadata := prepared.1
  linked := prepared.2.1
  intervals := GeneralDictionarySupportRecursiveExample.initial_source.intervals
  below_seed := GeneralDictionarySupportRecursiveExample.initial_source.below_seed
  unallocated := rfl

theorem before_scheduled : GeneralDictionaryEarlyMergeChoices.Scheduled registry displayRoot before :=
  .install (.initial (context true) source) packet [] .root enabled novel packet_guard

theorem before_model : Models before.current model :=
  (GeneralNominalFeedbackSites.install_models (start displayRoot).current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl model).mpr
    ⟨(initial_models ..).mpr (state_models true),branch⟩

noncomputable abbrev site (n : Nat) := GeneralNominalFeedbackSites.childSite packet (child n)

theorem site_present (n : Nat) (which : n = 10 ∨ n = 11) : site n ∈ before.current.sites := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨child n,?_,rfl⟩
  change child n ∈ children
  rw [children_exact]
  rcases which with rfl | rfl <;> simp

private theorem recovered_origin (n : Nat) : ∃ origin,
    (GeneralNominalFeedbackSites.recover before.current (site n)).inputs = [some origin] := by
  classical
  have equal : GeneralNominalFeedbackSites.EndpointEqual before.current ((1 : Nat),1) :=
    fun _ _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  have existsOrigin : ∃ origin, GeneralNominalFeedbackSites.recoverOrigin before.current (site n) (0 : Fin 1) = some origin := by
    unfold GeneralNominalFeedbackSites.recoverOrigin
    split
    · exact ⟨_,rfl⟩
    · change ∃ origin, (if GeneralNominalFeedbackSites.EndpointEqual before.current (1,1)
        then some (Origin.source 1) else none) = some origin
      rw [ite_eq_left equal]
      exact ⟨_,rfl⟩
  obtain ⟨origin,found⟩ := existsOrigin
  refine ⟨origin,?_⟩
  change List.ofFn (fun i : Fin 1 => GeneralNominalFeedbackSites.recoverOrigin before.current (site n) i) = [some origin]
  simp only [List.ofFn_succ,List.ofFn_zero]
  rw [found]

/-- Inputs are equal by the source point interval, irrespective of which
retained provenance origin classical search returns. -/
theorem inputs_same : GeneralNominalFeedbackSites.SameInputs before.current (site 10) (site 11) := by
  obtain ⟨a,left⟩ := recovered_origin 10
  obtain ⟨b,right⟩ := recovered_origin 11
  refine ⟨rfl,?_⟩
  change GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related (Models before.current)) _ _
  rw [left,right]
  refine .cons ⟨a,b,rfl,rfl,?_⟩ .nil
  intro m valid
  have first := GeneralNominalFeedbackSites.recover_sound before.current (site 10) m valid
    (valid.2.2 (site 10) (site_present 10 (Or.inl rfl))) (0 : Fin 1) a (by rw [left]; rfl)
  have last := GeneralNominalFeedbackSites.recover_sound before.current (site 11) m valid
    (valid.2.2 (site 11) (site_present 11 (Or.inr rfl))) (0 : Fin 1) b (by rw [right]; rfl)
  refine ⟨first.1,last.1,?_⟩
  intro x y hx hy
  have fx := first.2 x hx
  have fy := last.2 y hy
  exact ⟨CommonNominalFullCarrier.subtype_trans fx.2 fy.1,
    CommonNominalFullCarrier.subtype_trans fy.2 fx.1⟩

noncomputable abbrev finish := GeneralNominalSupportSteps.merge before (site 10) (site 11)
  (GeneralNominalSupportChoices.dependencyPool before)

theorem actual_early_merge : GeneralDictionaryEarlyMergeChoices.Scheduled registry displayRoot finish ∧
    Step registry displayRoot before finish ∧ finish.current.packets ≠ [] ∧ finish.current.aliases ≠ [] := by
  apply GeneralDictionaryEarlyMergeBoundary.initial_install_merge registry displayRoot (context true) source packet []
    rfl enabled novel packet_guard (child 10)
  · change child 10 ∈ children; rw [children_exact]; simp
  · decide +kernel
  · exact site_present 11 (Or.inr rfl)
  · intro equal
    have same := (GeneralNominalIdentities.source_identity (state true).seed _ _).mp equal
    have impossible := congrArg (fun x : GeneralNominalIdentities.Origin => x.2.2.2.1) same
    contradiction
  · exact inputs_same

theorem finish_model : Models finish.current model := by
  apply (merge_models before.current (site 10) (site 11) model).mpr
  refine ⟨before_model,?_⟩
  apply (GeneralNominalDemandMerging.output_atoms_exact (site 10) (site 11) model).mpr
  intro a ha b hb same
  have one := List.mem_singleton.mp ha
  have two := List.mem_singleton.mp hb
  subst a; subst b
  have nonzero (n : Nat) : outputTarget n ≠ 0 := by
    have positive := GeneralNominalIdentities.source_above_seed (state true).seed
      (GeneralNominalAllocation.origin 100 1 5 (n+20) 0)
    unfold outputTarget GeneralNominalAllocation.source
    omega
  simp only [nonzero]
  exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem actual_path : B4Target.Steps (Step registry displayRoot) (start displayRoot) finish :=
  .tail (.tail .refl ⟨displayRoot,.root,.install packet [] enabled novel packet_guard⟩) actual_early_merge.2.1

theorem reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish :=
  ⟨start displayRoot,⟨context true,source,rfl⟩,actual_path⟩

/-- Concrete inhabited source path with a genuine alias-adding merge after a
nonempty installation. The two newly emitted child classes are uncommitted;
this does NOT exemplify merging two classes both carrying recorded packets. -/
theorem inhabited_early_merge :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧ finish.current.aliases ≠ [] ∧
    GeneralDictionarySupportChoices.Coherent finish.current :=
  ⟨reachable,finish_model,actual_early_merge.2.2.1,actual_early_merge.2.2.2,
    GeneralDictionaryEarlyMergeChoices.scheduled_coherent registry displayRoot finish actual_early_merge.1⟩

theorem output_atoms_exact :
    GeneralNominalDemandMerging.outputAtoms (site 10) (site 11) =
      [.tyLe (.var (outputTarget 10)) (.var (outputTarget 11)),
       .tyLe (.var (outputTarget 11)) (.var (outputTarget 10))] := rfl

theorem output_targets_distinct : outputTarget 10 ≠ outputTarget 11 := by
  intro equal
  have same := (GeneralNominalIdentities.source_identity (state true).seed _ _).mp equal
  have impossible := congrArg (fun x : GeneralNominalIdentities.Origin => x.2.2.2.1) same
  contradiction

theorem finish_sourceformed : SourceFormed registry displayRoot finish :=
  .update (.update (.initial (context true) source)
    ⟨displayRoot,.root,.install packet [] enabled novel packet_guard⟩) actual_early_merge.2.1

/-- Both output identities are genuinely distinct and both directed equations
are added on the reachable support path. Only the parent is recorded; child
Joint, child dictionaries, and two committed classes are not asserted. -/
theorem reachable_nonempty_output_merge :
    SourceFormed registry displayRoot finish ∧
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    outputTarget 10 ≠ outputTarget 11 ∧
    GeneralNominalDemandMerging.outputAtoms (site 10) (site 11) ≠ [] := by
  refine ⟨finish_sourceformed,reachable,finish_model,output_targets_distinct,?_⟩
  rw [output_atoms_exact]
  simp

theorem terminal_report :
    report (context true) terminal [(1,1)] =
      {captures := [⟨0,(1,1),none⟩],checked := [(1,1),(1,1)]} := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,inspectMany,inspect,Report.append]

theorem terminal_schema (n : Nat) :
    generated registry (context true) (child n) terminal terminal_checked [(1,1)] =
      {tests := [(.source (outputTarget n),.scalar .int)]} := by
  unfold generated GeneralNominalMaterialization.requests
  rw [GeneralDictionaryJointMergeExample.emissions_empty]
  simp [GeneralNominalMaterialization.rootRequests,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,normalize,normalizeArgs,
    GeneralNominalExamples.interpretation]

theorem terminal_branch (n : Nat) :
    BranchModels registry (context true) (child n) terminal terminal_checked [(1,1)] model := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [terminal_report]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨state_models true,?_,?_⟩
      · intro first one last two _
        have a := List.mem_singleton.mp one
        have b := List.mem_singleton.mp two
        subst first; subst last
        exact CommonNominalFullCarrier.subtype_refl _
      · simp [GeneralNominalAllocation.merges,bindings,GeneralNominalAllocation.occurrences,
          Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All,PresenceNormalForm.Atom.Holds,
        CommonNominalFullCarrier.model,CommonNominalFullCarrier.subtype_refl]
  · rw [terminal_report]
    simp [ProjectionModels]
  · rw [terminal_schema]
    refine ⟨?_,by simp,by simp,by simp⟩
    intro test member
    have eq := List.mem_singleton.mp member; subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observation
    cases observation
    simp only [Test.Holds,output_nonzero]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem terminal_instance (n : Nat) :
    GeneralDictionaryRecursiveEvidence.Instance registry (context true) model (child n) 7 [] := by
  refine ⟨terminal,by simp,terminal_checked,rfl,rfl,[(1,1)],?_,?_,?_,?_,prepared.1,terminal_branch n⟩
  · change arguments (context true) (GeneralDictionaryJointMergeExample.root 0 0) = some [(1,1)]
    decide +kernel
  · rw [terminal_report]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have eq := List.mem_singleton.mp member; subst output
      exact ⟨GeneralDictionaryJointMergeExample.outputEquation,by simp,rfl⟩
    · rw [terminal_schema]
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    rw [GeneralDictionaryJointMergeExample.emissions_empty]
    rfl

theorem final_extension :
    GeneralDictionaryOrdinaryTrace.Extension (context true) finish.current.context :=
  GeneralDictionaryOrdinaryTrace.extension_trans (GeneralDictionaryOrdinaryTrace.packet_extension packet)
    (GeneralDictionaryOrdinaryTrace.merge_extension before.current (site 10) (site 11))

theorem current_terminal_instance (n : Nat) :
    GeneralDictionaryRecursiveEvidence.Instance registry finish.current.context model (child n) 7 [] :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry (context true) finish.current.context final_extension
    model finish_model.1 (child n) 7 [] (terminal_instance n)

noncomputable abbrev current := finish.current.context

theorem output_reserved (n : Nat) (which : n = 10 ∨ n = 11) :
    outputTarget n ∈ GeneralNominalAllocation.reserved (state true) registry displayRoot.identity := by
  apply List.mem_map.mpr
  refine ⟨GeneralNominalAllocation.origin 100 1 5 (n+20) 0,?_,rfl⟩
  rcases which with rfl | rfl <;>
    simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys,
      Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]

theorem sources_shape (identity : Nat) (member : identity ∈ GeneralNominalState.sources current.state) :
    identity = 0 ∨ identity = 1 ∨
      identity ∈ GeneralNominalAllocation.reserved (state true) registry displayRoot.identity := by
  simp only [GeneralNominalState.sources] at member
  change identity ∈ (([0,1] ++ [0,1]) ++ GeneralNominalAllocation.reserved (state true) registry displayRoot.identity) ++ _ at member
  rcases List.mem_append.mp member with old | ordinary
  · rcases List.mem_append.mp old with base | allocated
    · simp at base
      rcases base with h | h | h | h <;> simp [h]
    · exact Or.inr (Or.inr allocated)
  · have shape : current.state.ordinary.flatMap GeneralNominalState.atomSources =
        [1,1,0,0,0,0,1,1,outputTarget 10,outputTarget 11,outputTarget 11,outputTarget 10] := by
      decide +kernel
    rw [shape] at ordinary
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ordinary
    rcases ordinary with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals first
      | exact Or.inl h
      | exact Or.inr (Or.inl h)
      | exact Or.inr (Or.inr (h ▸ output_reserved 10 (Or.inl rfl)))
      | exact Or.inr (Or.inr (h ▸ output_reserved 11 (Or.inr rfl)))

theorem current_fresh (identity : Nat) : GeneralNominalAllocation.Fresh current.state registry identity := by
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

theorem child_linked (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralNominalState.Linked current.state (child n).demand := by
  constructor
  · intro index
    have member : 1 ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))
    exact ⟨member,member⟩
  · intro output member
    have eq := List.mem_singleton.mp member; subst output
    unfold GeneralNominalState.sources
    apply List.mem_append_left
    apply List.mem_append_right
    exact output_reserved n which

theorem child_branch_at (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralNominalJointCandidates.BranchAt registry finish.current (child n) 7 model := by
  obtain ⟨d,visible,checked,key,role,bounds,located,finished,ready,emitted,metadata,branch⟩ :=
    current_terminal_instance n
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · contradiction
  · refine ⟨terminal,by simp,checked,key,role,?_,bounds,located,branch⟩
    exact ⟨metadata,child_linked n which,current_fresh _,bounds,located,finished,ready,model,branch⟩

theorem old_alias_eq {a b : Nat} (related : Alias before.current a b) : a = b := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem first_not_parent : (child 10).identity ≠ displayRoot.identity := by decide +kernel
theorem last_not_parent : (child 11).identity ≠ displayRoot.identity := by decide +kernel

theorem sites_exact : finish.current.sites =
    [GeneralNominalDemandMerging.pointSite displayRoot,site 10,site 11] := by
  change [GeneralNominalDemandMerging.pointSite displayRoot] ++
    children.map (GeneralNominalFeedbackSites.childSite packet) = _
  rw [children_exact]
  rfl

theorem merged_alias_identity (identity : Nat)
    (related : Alias finish.current (child 10).identity identity) :
    (child 10).identity = identity ∨ (child 11).identity = identity := by
  rcases (GeneralDictionaryJointMerge.alias_merge_first_iff before.current (site 10) (site 11) identity).mp related with left | right
  · exact Or.inl (old_alias_eq left)
  · exact Or.inr (old_alias_eq right)

theorem merged_child_joint :
    GeneralNominalJointCandidates.Joint registry finish.current (child 10) 7 := by
  refine ⟨?_,model,finish_model,child_branch_at 10 (Or.inl rfl),?_⟩
  · intro committed member related
    have eq := List.mem_singleton.mp member; subst committed
    rcases merged_alias_identity _ related with left | right
    · exact False.elim (first_not_parent left)
    · exact False.elim (last_not_parent right)
  · intro childSite related
    have member := related.1
    rw [sites_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · rcases merged_alias_identity _ related.2 with left | right
      · exact False.elim (first_not_parent left)
      · exact False.elim (last_not_parent right)
    · exact child_branch_at 10 (Or.inl rfl)
    · exact child_branch_at 11 (Or.inr rfl)

theorem merged_child_evidence (n : Nat) :
    GeneralDictionaryRecursiveEvidence.Evidence registry current model (child n) (.node 7 []) := by
  apply (GeneralDictionaryRecursiveEvidence.evidence_iff_payload ..).mpr
  exact .node (current_terminal_instance n) .nil

/-- One inhabited reachable nonempty merge and the two complete current source
dictionaries now coexist in the SAME fixture and SAME model. The children are
still uncommitted, and no global V5 completeness or Stable claim follows. -/
theorem reachable_joint_evidence :
    SourceFormed registry displayRoot finish ∧
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    GeneralNominalJointCandidates.Joint registry finish.current (child 10) 7 ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry current model (child 10) (.node 7 []) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry current model (child 11) (.node 7 []) ∧
    outputTarget 10 ≠ outputTarget 11 ∧
    GeneralNominalDemandMerging.outputAtoms (site 10) (site 11) ≠ [] := by
  refine ⟨finish_sourceformed,reachable,finish_model,merged_child_joint,
    merged_child_evidence 10,merged_child_evidence 11,output_targets_distinct,?_⟩
  rw [output_atoms_exact]
  simp

end Yulang.GeneralDictionaryOutputMergeSuccess
