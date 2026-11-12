import Yulang.GeneralDictionaryFeedbackEvidence
import Yulang.GeneralNominalFeedbackRegressions

/-! A raw, inhabited journal may retain an invisible stale key. This tests the
sufficient ModeledSelectedJoint condition, not the source Evidence judgment.
No source formation or reachability is asserted. -/
namespace Yulang.GeneralDictionaryModeledJointGap
open GeneralDeclarations GeneralSourceDictionaries GeneralDeclarationPatterns
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalRecursiveExamples (len lenRegistry len_checked)

abbrev context := GeneralNominalExamples.context true
abbrev root : Occurrence roles := ⟨200,⟨3,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
abbrev stale : Declaration := { len with id := 31 }
theorem stale_checked : DeclarationChecked constructors roles stale := by
  rcases len_checked with ⟨a,b,c,d,e,f,g,h,i,j⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j⟩
abbrev packet : Packet roles := ⟨lenRegistry,context,GeneralNominalDemandMerging.pointSite root,stale,stale_checked,[(0,0)]⟩
abbrev journal : State roles := { context := context, packets := [packet], sites := [GeneralNominalDemandMerging.pointSite root] }

theorem query (identity : Nat) : GeneralNominalInspection.queries context.state context.interpretation { len with id := identity } = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem schema (identity : Nat) (checked : DeclarationChecked constructors roles { len with id := identity }) :
    generated lenRegistry context root { len with id := identity } checked [(0,0)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem every_branch (identity : Nat) (checked : DeclarationChecked constructors roles { len with id := identity })
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    BranchModels lenRegistry context root { len with id := identity } checked [(0,0)] model := by
  have privateModel := private_models context lenRegistry root { len with id := identity } 0
    GeneralNominalExamples.listDescriptor rfl 0 rfl (1,1) rfl (query identity) model valid
  refine ⟨privateModel.1,privateModel.2,?_⟩
  rw [schema]
  exact GeneralNominalMaterialization.empty_models ..

theorem models_iff (model : GeneralNominalCommonBridge.Assignment) :
    Models journal model ↔ GeneralNominalState.Models context.state model := by
  constructor
  · exact fun valid => valid.1
  · intro valid
    refine ⟨valid,?_,?_⟩
    · intro p member
      have same := List.mem_singleton.mp member
      subst p
      exact every_branch 31 stale_checked model valid
    · intro s member
      have same := List.mem_singleton.mp member
      subst s
      exact point_holds root model

theorem journal_model : Models journal GeneralNominalExamples.model :=
  (models_iff _).mpr (GeneralNominalExamples.state_models true)

theorem known (source : Nat) (member : source ∈ GeneralNominalState.sources context.state) :
    GeneralNominalState.Known context.state source := by
  have alternatives : source = 0 ∨ source = 1 := by
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]
  rcases alternatives with rfl | rfl
  · exact ⟨0,rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩
  · exact ⟨1,rfl,Or.inl (by decide +kernel)⟩

theorem generated_only_root (child : Occurrence roles) (generated : Generated journal root child) : child = root := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same := List.mem_singleton.mp member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence same

theorem no_install (p : Packet roles) (same : p.site.occurrence = root) :
    ¬ GeneralNominalFeedbackSteps.Installable lenRegistry journal p := by
  intro enabled
  have visible := enabled.1.2.2.2.1
  have declaration : p.declaration = len := List.mem_singleton.mp visible
  have compatible := enabled.1.2.2.2.2.2.2.2.2.1
  have alias : Alias journal p.site.occurrence.identity packet.site.occurrence.identity := by
    rw [same]
    exact .refl 200
  have conflict := compatible packet (List.mem_singleton_self _) alias
  rw [declaration] at conflict
  cases conflict

theorem stable : GeneralNominalFeedbackSteps.Stable lenRegistry journal root := by
  intro focus generated after update
  have same := generated_only_root focus generated
  cases update with
  | enqueue focus _ absent => exact absent _ (List.mem_singleton_self _) same.symm
  | install p enabled _ => exact no_install p same enabled
  | merge first last one two _ novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)
  | refresh _ _ _ source member unknown _ => exact unknown (known source member)
  | equate _ first last _ _ equal novel =>
    exact novel (fun model valid => equal model ((models_iff model).mpr valid))

theorem not_joint : ¬ GeneralNominalJointCandidates.Joint lenRegistry journal root 30 := by
  intro joint
  have bad := joint.1 packet (List.mem_singleton_self _) (.refl 200)
  cases bad

private theorem int_not_nominal (name : Nat) (arguments : List Argument) : ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

theorem edge_shape (first last : Nat) (edge : GeneralNominalFeedbackK2.Edge journal first last) : first = 0 ∧ last = 1 := by
  have lastCases : last = 0 ∨ last = 1 := by
    have member := edge.2.1
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]
  rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_,_⟩,_,_⟩ | ⟨name,index,observed⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,equal⟩ := observed GeneralNominalExamples.model journal_model
    cases seen with
    | argument source compared found =>
      cases source
      have zero : first = 0 := by
        by_cases zero : first = 0
        · exact zero
        · exact False.elim (int_not_nominal _ _ (by simpa [GeneralNominalExamples.model,zero] using compared.1))
      subst first
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
      have size := invariant.2.1
      have indexZero : index = 0 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        simp only [List.length_cons,List.length_nil] at size
        omega
      subst index
      have arg := invariant.2.2 0 (.inl (.base .int)) (.inl actual) rfl found
      refine ⟨rfl,?_⟩
      rcases lastCases with rfl | one
      · exact False.elim (int_not_nominal _ _ (subtype_trans arg.1 equal.1))
      · exact one

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle journal source := by
  rintro ⟨next,edge,path⟩
  have shape := edge_shape source next edge
  cases path with
  | nil => omega
  | cons second _ => have another := edge_shape _ _ second; omega

private theorem old_edge (first last : Fin 2) (edge : GeneralNominalMixedRecurrence.Edge context.state first last) :
    GeneralNominalFeedbackK2.Edge journal first.val last.val := by
  refine ⟨?_,?_,?_⟩
  · simp [GeneralNominalState.sources,List.ofFn_succ]; omega
  · simp [GeneralNominalState.sources,List.ofFn_succ]; omega
  · rcases edge with ⟨kind,_,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument journal first last argument)

private theorem old_path (first last : Fin 2) (path : GeneralNominalMixedRecurrence.Path context.state first last) :
    GeneralNominalFeedbackK2.Path journal first.val last.val := by
  exact GeneralNominalMixedRecurrence.Path.rec
    (motive := fun first last _ => GeneralNominalFeedbackK2.Path journal first.val last.val)
    (fun _ => .nil _) (fun edge _ ih => .cons (old_edge _ _ edge) ih) path

theorem old_acyclic (slot : Fin 2) : ¬ GeneralNominalCycleK2.RecursAt context.state slot := by
  intro recurrent
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurrent
  exact acyclic slot.val ⟨next.val,old_edge _ _ edge,old_path _ _ path⟩

theorem report_calculated : report context len [(0,0)] = captured context.state 0 0 0 (1,1) :=
  report_exact context len 0 GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl (query 30)

theorem linked : GeneralNominalState.Linked context.state root.demand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro output member; cases member

theorem prepared : Prepared lenRegistry context root len len_checked := by
  refine ⟨?_,linked,initial_fresh _ _ _ (by decide +kernel),[(0,0)],(by decide +kernel),?_,?_,
    GeneralNominalExamples.model,every_branch 30 len_checked _ (GeneralNominalExamples.state_models true)⟩
  · refine ⟨rfl,?_⟩
    intro name primitive recorded
    by_cases two : name = 2
    · subst name
      have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
      subst primitive
      exact ⟨⟨[],2⟩,rfl,rfl⟩
    · simp [two] at recorded
  · rw [report_calculated]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ h; cases h),?_⟩
    rw [schema 30]

theorem ready : ¬ GeneralNominalState.RootPending context.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown (known 0 (by simp [GeneralNominalState.sources,List.ofFn_succ]))

theorem survivor : Survivor lenRegistry context root 30 [] := by
  refine ⟨ready,len,by simp,len_checked,rfl,rfl,[(0,0)],(by decide +kernel),prepared,?_⟩
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    GeneralDeclarationDemands.emitAll]

theorem selected : GeneralNominalFeedbackK2.Local lenRegistry journal root (.selected 30 []) := by
  refine .selected ⟨ready,?_,?_,?_⟩ ⟨survivor,?_⟩
  · rintro (⟨_,_,_,slot,_,recurs⟩ | ⟨_,_,_,cycle,_⟩)
    · exact old_acyclic slot recurs
    · exact acyclic _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
    · exact old_acyclic visited.1 recurs
    · exact acyclic _ cycle
  · rintro (⟨_,declaration,visible,checked,_,_,unprepared⟩ | ⟨_,legacy⟩)
    · have same := List.mem_singleton.mp visible
      subst declaration
      exact unprepared prepared
    · rcases legacy with ⟨rootK2,_⟩ | ⟨candidateK2,_⟩
      · obtain ⟨_,_,index,slot,_,recurs⟩ := rootK2
        exact GeneralNominalMixedRecurrence.nominal_not_recursive context.state 0 GeneralNominalExamples.listDescriptor rfl
          (by have same : slot = 0 := Fin.ext ‹_›; simpa only [same] using recurs)
      · obtain ⟨_,declaration,visible,_,_,_,bounds,located,visited,member,recurs⟩ := candidateK2
        have same := List.mem_singleton.mp visible
        subst declaration
        have found : arguments context root = some [(0,0)] := by decide +kernel
        have equal := Option.some.inj (found.symm.trans located)
        subst bounds
        rw [report_calculated] at member
        have equal := List.mem_singleton.mp member
        subst visited
        exact GeneralNominalMixedRecurrence.nominal_not_recursive context.state 0 GeneralNominalExamples.listDescriptor rfl recurs
  · intro key children given
    have copy := given
    obtain ⟨_,d,visible,_,identity,_⟩ := given
    have same := List.mem_singleton.mp visible
    subst d
    refine ⟨identity.symm,?_⟩
    subst key
    have checked : Checked lenRegistry := ⟨by decide +kernel,by intro d h; have e := List.mem_singleton.mp h; subst d; exact len_checked⟩
    exact survivor_children_functional lenRegistry checked context root 30 children [] copy survivor

theorem modeled_stable_selected_not_joint :
    GeneralNominalFeedbackSteps.Stable lenRegistry journal root ∧
    GeneralNominalFeedbackK2.Local lenRegistry journal root (.selected 30 []) ∧
    Models journal GeneralNominalExamples.model ∧
    ¬ GeneralNominalJointCandidates.Joint lenRegistry journal root 30 :=
  ⟨stable,selected,journal_model,not_joint⟩

theorem registry_checked : Checked lenRegistry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  have same := List.mem_singleton.mp member
  subst declaration
  exact len_checked

/-- This disproves the proposed sufficient residual on the actual feedback
boundary, even with a model witness. It does not refute EvidenceNode. -/
theorem no_modeledSelectedJoint : ¬ GeneralDictionaryFeedbackEvidence.ModeledSelectedJoint roles := by
  intro claimed
  exact not_joint (claimed lenRegistry ⟨rfl,registry_checked⟩ journal root 30 [] stable selected ⟨_,journal_model⟩)

theorem current_instance (model : GeneralNominalCommonBridge.Assignment) (valid : Models journal model) :
    GeneralDictionaryRecursiveEvidence.Instance lenRegistry context model root 30 [] := by
  exact GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch lenRegistry registry_checked context model
    root 30 [] survivor len (List.mem_singleton_self _) len_checked rfl [(0,0)] (by decide +kernel)
    (every_branch 30 len_checked model valid.1)

/-- The actual source dictionary still exists for every journal model: stale
key coherence is strictly stronger than this semantic evidence property. -/
theorem current_evidence (model : GeneralNominalCommonBridge.Assignment) (valid : Models journal model) :
    GeneralDictionaryRecursiveEvidence.Evidence lenRegistry context model root (.node 30 []) :=
  (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff lenRegistry context model root 30).mpr (current_instance model valid)

/-- The counterexample is a raw state, not a reachable well-formed source state.
The invisible key is ruled out by the existing source formation invariant. -/
theorem not_sourceFormed : ¬ GeneralNominalFeedbackSteps.SourceFormed lenRegistry root journal := by
  intro formed
  have source := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances lenRegistry root journal formed
    packet (List.mem_singleton_self _)).1 GeneralNominalExamples.model journal_model
  obtain ⟨declaration,visible,_,identity,_⟩ := source
  have same := List.mem_singleton.mp visible
  subst declaration
  cases identity

end Yulang.GeneralDictionaryModeledJointGap
