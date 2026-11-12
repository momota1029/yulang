import Yulang.GeneralDictionaryEarlyMergeBoundary
import Yulang.GeneralDictionarySupportRecursiveExample

/-! Two distinct where occurrences with identical captured inputs. -/
namespace Yulang.GeneralDictionaryEarlyMergeScalarExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation intDisplay int_display_checked)

abbrev secondClause : Clause := ⟨11, 0, [.var 0], []⟩
abbrev declaration : Declaration := { GeneralDeclarationExamples.display with
  requirements := [GeneralDeclarationExamples.displayChild, secondClause] }
abbrev registry : Registry := ⟨constructors, roles, [declaration,intDisplay]⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature, Clause.Signature, roles, GeneralDeclarationExamples.bareRole]
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
  · exact int_display_checked

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

theorem schema : generated registry (context true) displayRoot declaration checked [(0,0)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair])]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,GeneralNominalMaterialization.generated]

theorem branch (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m) :
    BranchModels registry (context true) displayRoot declaration checked [(0,0)] m := by
  have privateModel := private_models (context true) registry displayRoot declaration 0 listDescriptor rfl 0 rfl (1,1) rfl query m valid
  refine ⟨privateModel.1,privateModel.2,?_⟩
  rw [schema]; exact GeneralNominalMaterialization.empty_models ..

theorem prepared : Prepared registry (context true) displayRoot declaration checked := by
  refine ⟨GeneralDictionarySupportRecursiveExample.initial_source.metadata,
    GeneralDictionarySupportRecursiveExample.initial_source.linked,
    initial_fresh _ _ _ (by decide +kernel),[(0,0)],rfl,?_,?_,model,branch model (state_models true)⟩
  · rw [report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query]
    exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ h; cases h),?_⟩; rw [schema]

noncomputable abbrev children := GeneralNominalAllocation.children (state true) registry displayRoot declaration checked
    (bindings (state true) (report (context true) declaration [(0,0)]))

theorem survivor : Survivor registry (context true) displayRoot 1 children :=
  ⟨GeneralNominalRecursiveExamples.display_survivor.1,declaration,by simp,checked,rfl,rfl,[(0,0)],rfl,prepared,rfl⟩

private theorem wrong_failed : Failed registry (context true) displayRoot intDisplay int_display_checked := by
  refine ⟨prepared.1,initial_fresh _ _ _ (by decide +kernel),[(0,0)],?_,?_,?_,Or.inl ?_⟩ <;> decide +kernel

theorem selected : GeneralNominalSupportBoundary.Local registry (start displayRoot) displayRoot (.selected 1 children) := by
  apply GeneralNominalSupportBoundary.selected_supported (support := []) _ (all_source_decisions displayRoot (fun _ => rfl))
  refine .selected ⟨survivor.1,no_root _,no_candidate _,?_⟩ ⟨survivor,?_⟩
  · rintro (⟨_,d,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · exact notPrepared prepared
      · exact notFailed wrong_failed
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
  · intro key cs found
    have original := found
    obtain ⟨_,d,visible,check,identity,role,bounds,located,ready,_⟩ := found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · have equal : key = 1 := identity.symm; subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked (context true) displayRoot 1 cs children original survivor⟩
    · exact False.elim (GeneralNominalLocalBoundary.recursive_failed_not_prepared registry (context true) displayRoot intDisplay check wrong_failed ready)

abbrev child (clause : Nat) : Occurrence roles :=
  ⟨GeneralNominalAllocation.source (state true) registry 100
    (GeneralNominalAllocation.origin 100 1 6 clause 0),
    ⟨0,fun _ => (1,1),[],by intro _ h; cases h⟩⟩

theorem children_exact : children = [child 10,child 11] := by
  unfold children
  rw [report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query]
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from
    (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair])]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    normalize,child,Declaration.outputNames,bindings,captured,GeneralNominalAllocation.allocation]

abbrev packet : Packet roles := ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,declaration,checked,[(0,0)]⟩
noncomputable abbrev before := GeneralNominalSupportSteps.install (start displayRoot) packet []

theorem enabled : GeneralNominalFeedbackSteps.Installable registry (start displayRoot).current packet := by
  have localRule := GeneralNominalSupportBoundary.selected_old selected
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],by simp,rfl,rfl,prepared,
    GeneralNominalFeedbackK2.selected_legacy localRule,?_,?_,?_,?_⟩,localRule,?_⟩
  · intro prior member; cases member
  · intro other member _; have eq := List.mem_singleton.mp member; subst other; exact .refl _
  · exact ⟨model,(initial_models ..).mpr (state_models true),branch model (state_models true)⟩
  · exact GeneralNominalJointCandidates.initial_joint registry (context true) displayRoot declaration
      (by simp) checked rfl [(0,0)] rfl prepared model (branch model (state_models true))
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
    ⟨(initial_models ..).mpr (state_models true),branch model (state_models true)⟩

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
  exact ⟨before_model,by intro atom member; cases member⟩

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

end Yulang.GeneralDictionaryEarlyMergeScalarExample
