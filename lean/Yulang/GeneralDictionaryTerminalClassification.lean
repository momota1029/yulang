import Yulang.GeneralDictionaryTerminalRefresh
/-! Actual final feedback selection and unchanged-boundary leaf classification
for the concrete source-formed stable terminal output example. -/
namespace Yulang.GeneralDictionaryTerminalClassification
open GeneralDictionaryTerminalRefresh
open GeneralDictionaryRecursiveObstruction (registry context root declaration declaration_checked)
open GeneralNominalSaturationState GeneralSourceDictionaries CommonNominalFullCarrier
open GeneralNominalRecursiveCandidates GeneralNominalUnaryCaptureFacts
open GeneralDeclarationExamples (roles)

private theorem int_not_nominal (name : Nat) (arguments : List Argument) : ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

theorem edge_shape (first last : Nat) (edge : GeneralNominalFeedbackK2.Edge refreshed first last) : first = 0 ∧ last = 1 := by
  rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_,_⟩,_,_⟩ | ⟨name,index,observed⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,equal⟩ := observed GeneralNominalExamples.model inhabited
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
      by_cases zero : last = 0
      · subst last
        exact False.elim (int_not_nominal _ _ (subtype_trans arg.1 equal.1))
      by_cases one : last = 1
      · exact one
      have large : 2 ≤ last := by omega
      obtain ⟨other,seen,equal⟩ := observed (varying last) (varying_model last large)
      cases seen with
      | argument source compared found =>
        cases source
        have atZero : (varying last 0).1 = nominal 0 [.inl (.base .int)] := by simp only [varying,ite_eq_right (show 0 ≠ last by omega)]; rfl
        rw [atZero] at compared
        have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
        have arg := invariant.2.2 0 (.inl (.base .int)) (.inl other) rfl found
        have atLast : (varying last last).1 = .base .str := by simp only [varying,ite_true]; rfl
        rw [atLast] at equal
        have impossible : Equivalent (.base .str) (.base .int) :=
          ⟨subtype_trans equal.2 arg.2,subtype_trans arg.1 equal.1⟩
        exact False.elim (GeneralDictionaryRecursiveObstruction.bad_output_equation impossible)
theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle refreshed source := by
  rintro ⟨next,edge,path⟩
  have shape := edge_shape source next edge
  cases path with
  | nil => omega
  | cons second _ => have another := edge_shape _ _ second; omega

private theorem old_edge (first last : Fin 2) (edge : GeneralNominalMixedRecurrence.Edge nextState first last) :
    GeneralNominalFeedbackK2.Edge refreshed first.val last.val := by
  refine ⟨?_,?_,?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨first,rfl⟩)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨last,rfl⟩)))
  · rcases edge with ⟨kind,_,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument refreshed first last argument)

private theorem old_path (first last : Fin 2) (path : GeneralNominalMixedRecurrence.Path nextState first last) :
    GeneralNominalFeedbackK2.Path refreshed first.val last.val := by
  exact GeneralNominalMixedRecurrence.Path.rec
    (motive := fun first last _ => GeneralNominalFeedbackK2.Path refreshed first.val last.val)
    (fun _ => .nil _) (fun edge _ ih => .cons (old_edge _ _ edge) ih) path

theorem old_acyclic (slot : Fin 2) : ¬ GeneralNominalCycleK2.RecursAt nextState slot := by
  intro recurrent
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurrent
  exact acyclic slot.val ⟨next.val,old_edge _ _ edge,old_path _ _ path⟩



theorem report_calculated : report nextContext declaration [(0,0)] = captured nextState 0 0 0 (1,1) :=
  report_exact nextContext declaration 0 GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl current_query

theorem prepared : Prepared registry nextContext root declaration declaration_checked := by
  refine ⟨GeneralDictionaryRecursiveObstruction.metadata,?_,?_,[(0,0)],rfl,?_,?_,_,every_current_branch _ inhabited⟩
  · constructor
    · intro index
      constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro key member _
    exact member
  · rw [report_calculated]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨GeneralDictionaryRecursiveObstruction.equation,by simp,rfl⟩
    · rw [current_schema]

theorem survivor : Survivor registry nextContext root 40 [] := by
  refine ⟨?_,declaration,by simp,declaration_checked,rfl,rfl,[(0,0)],rfl,prepared,?_⟩
  · rintro ⟨index,unknown⟩
    exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
    rfl

theorem selected : GeneralNominalFeedbackK2.Local registry refreshed root (.selected 40 []) := by
  refine .selected ⟨survivor.1,?_,?_,?_⟩ ⟨survivor,?_⟩
  · rintro (⟨_,_,_,slot,_,recurs⟩ | ⟨_,_,_,cycle,_⟩)
    · exact old_acyclic slot recurs
    · exact acyclic _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
    · exact old_acyclic visited.1 recurs
    · exact acyclic _ cycle
  · rintro (⟨_,decl,visible,checked,_,_,unprepared⟩ | ⟨_,legacy⟩)
    · have same := List.mem_singleton.mp visible
      subst decl
      exact unprepared prepared
    · rcases legacy with ⟨rootK2,_⟩ | ⟨candidateK2,_⟩
      · obtain ⟨_,_,index,slot,equal,recurs⟩ := rootK2
        have same : slot = (0 : Fin 2) := Fin.ext equal
        subst slot
        exact GeneralNominalMixedRecurrence.nominal_not_recursive nextState 0 GeneralNominalExamples.listDescriptor rfl recurs
      · obtain ⟨_,decl,visible,_,_,_,bounds,located,visited,member,recurs⟩ := candidateK2
        have same := List.mem_singleton.mp visible
        subst decl
        have found : arguments nextContext root = some [(0,0)] := rfl
        have equal := Option.some.inj (found.symm.trans located)
        subst bounds
        change visited ∈ (report nextContext declaration [(0,0)]).inspected at member
        rw [report_calculated] at member
        have equal := List.mem_singleton.mp member
        subst visited
        exact GeneralNominalMixedRecurrence.nominal_not_recursive nextState 0 GeneralNominalExamples.listDescriptor rfl recurs
  · intro key children given
    have original := given
    obtain ⟨_,decl,visible,_,identity,_⟩ := given
    have same := List.mem_singleton.mp visible
    subst decl
    have same : key = 40 := identity.symm
    subst key
    exact ⟨rfl,survivor_children_functional registry GeneralDictionaryRecursiveObstruction.registry_checked nextContext root 40 children [] original survivor⟩

/-- Complete concrete resolution uses actual final classification as well as
source formation, stability, nonvacuity and current source evidence. -/
theorem resolved : GeneralNominalFeedbackSteps.SourceFormed registry root refreshed ∧
    GeneralNominalFeedbackSteps.Stable registry refreshed root ∧
    GeneralNominalFeedbackK2.Local registry refreshed root (.selected 40 []) ∧
    Models refreshed GeneralNominalExamples.model ∧
    (∀ m, Models refreshed m → GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.context m root (.node 40 [])) :=
  ⟨formed,stable,selected,inhabited,current_evidence⟩

theorem boundary_local : B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles)
    registry refreshed root (.selected 40 []) :=
  (GeneralNominalFeedbackBoundary.local_correspondence roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry refreshed root (.selected 40 [])).mpr selected

/-- Concrete final leaf classification on the unchanged boundary, not a
uniform executor or general termination theorem. -/
theorem classified : B4TargetV3.Classify (GeneralDictionaryFeedbackEvidence.boundary roles)
    registry refreshed root (.selected (.node 40 [])) := by
  have localRule := selected
  cases localRule with
  | selected safe unique => exact .selected safe unique .nil
/-- The concrete resolved state is reached by exactly the exhibited installation
and view-changing refresh, using the full actual feedback step relation. -/
theorem two_steps : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root)
    (GeneralNominalSaturationState.initial context root) refreshed :=
  .tail (.tail .refl GeneralDictionaryJournalTreeExamples.feedback_step) actual_refresh

end Yulang.GeneralDictionaryTerminalClassification
