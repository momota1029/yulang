import Yulang.GeneralDictionaryJournalTree
import Yulang.GeneralDictionaryCommittedEvidenceExamples
/-! Nonvacuous actual feedback installation of terminal key 40, followed by
uniform current-context journal-tree readback. The associated int output
excludes the old string countermodel. No transition is redefined. -/
namespace Yulang.GeneralDictionaryJournalTreeExamples
open GeneralDeclarationExamples (roles)
open GeneralDictionaryRecursiveObstruction
open GeneralDictionaryCommittedEvidenceExamples (packet before packet_children)
open GeneralNominalSaturationState GeneralSourceDictionaries CommonNominalFullCarrier

theorem good_before : Models before GeneralNominalExamples.model :=
  (initial_models context root _).mpr (GeneralNominalExamples.state_models false)

private theorem int_not_nominal (name : Nat) (arguments : List Argument) : ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

theorem edge_shape (first last : Nat) (edge : GeneralNominalFeedbackK2.Edge before first last) : first = 0 ∧ last = 1 := by
  have lastCases : last = 0 ∨ last = 1 := by
    have member := edge.2.1
    simp [before,initial,GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]
  rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_,_⟩,_,_⟩ | ⟨name,index,observed⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,equal⟩ := observed GeneralNominalExamples.model good_before
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

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle before source := by
  rintro ⟨next,edge,path⟩
  have shape := edge_shape source next edge
  cases path with
  | nil => omega
  | cons second _ => have another := edge_shape _ _ second; omega

private theorem old_edge (first last : Fin 2) (edge : GeneralNominalMixedRecurrence.Edge context.state first last) :
    GeneralNominalFeedbackK2.Edge before first.val last.val := by
  refine ⟨?_,?_,?_⟩
  · simp [before,initial,GeneralNominalState.sources,List.ofFn_succ]; omega
  · simp [before,initial,GeneralNominalState.sources,List.ofFn_succ]; omega
  · rcases edge with ⟨kind,_,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument before first last argument)

private theorem old_path (first last : Fin 2) (path : GeneralNominalMixedRecurrence.Path context.state first last) :
    GeneralNominalFeedbackK2.Path before first.val last.val := by
  exact GeneralNominalMixedRecurrence.Path.rec
    (motive := fun first last _ => GeneralNominalFeedbackK2.Path before first.val last.val)
    (fun _ => .nil _) (fun edge _ ih => .cons (old_edge _ _ edge) ih) path

theorem old_acyclic (slot : Fin 2) : ¬ GeneralNominalCycleK2.RecursAt context.state slot := by
  intro recurrent
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurrent
  exact acyclic slot.val ⟨next.val,old_edge _ _ edge,old_path _ _ path⟩


theorem selected : GeneralNominalFeedbackK2.Local registry before root (.selected 40 []) := by
  refine .selected ⟨not_pending,?_,?_,?_⟩ unique
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
    · rcases legacy with ⟨bad,_⟩ | ⟨bad,_⟩
      · exact not_rootK2 bad
      · exact not_candidateK2 bad


noncomputable abbrev after : State roles := GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)

theorem enabled : GeneralNominalFeedbackSteps.Installable registry before packet := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨rfl,rfl,by simp [before,initial],by simp,rfl,by decide +kernel,prepared,?_,?_,?_,?_,?_⟩
    · rw [packet_children]
      exact GeneralNominalFeedbackK2.selected_legacy selected
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member
      subst other
      exact .refl _
    · exact ⟨_,good_before,good_branch⟩
    · exact GeneralNominalJointCandidates.initial_joint registry context root declaration (by simp)
        declaration_checked rfl [(0,0)] (by decide +kernel) prepared _ good_branch
  · rw [packet_children]; exact selected
  · intro other member _
    have same := List.mem_singleton.mp member
    subst other
    exact .refl _

theorem feedback_step : GeneralNominalFeedbackSteps.Step registry root before after := by
  refine ⟨root,.root,.install packet enabled ?_⟩
  intro committed
  exact bad_not_branch (committed.1 badModel ((initial_models context root _).mpr bad_original_model))

theorem finished_step : GeneralDictionaryFinishedTrace.Step registry root before after :=
  .ordinary ⟨feedback_step,GeneralDictionaryOrdinaryTrace.packet_extension packet⟩

theorem no_child (child parent : Occurrence roles) : ¬ GeneralDictionaryJournalTree.Child after child parent := by
  rintro ⟨p,member,_,present⟩
  have same : p = packet := List.mem_singleton.mp member
  subst p
  rw [packet_children] at present
  cases present

theorem covered : GeneralDictionaryJournalTree.Covered after root := by
  intro site reached
  cases reached with
  | root => exact ⟨packet,List.mem_singleton_self _,rfl⟩
  | child _ child => exact False.elim (no_child _ _ child)

theorem accessible : Acc (GeneralDictionaryJournalTree.Child after) root :=
  .intro root (fun child relation => False.elim (no_child child root relation))

theorem good_after : Models after GeneralNominalExamples.model :=
  (GeneralNominalFeedbackSites.install_models before packet _ rfl _).mpr ⟨good_before,good_branch⟩

theorem bad_excluded : ¬ Models after badModel := by
  intro valid
  exact bad_not_branch ((GeneralNominalFeedbackSites.install_models before packet _ rfl _).mp valid).2

theorem uniform_dictionary :
    ∃ tree : Dictionary roles, tree.root = root ∧ GeneralSourceDictionaries.Evidence
      (GeneralDictionaryJournalTree.Recorded after) tree ∧
      ∀ model, Models after model → GeneralDictionaryRecursiveEvidence.Evidence registry after.context model root (erase tree) :=
  GeneralDictionaryJournalTree.uniform_dictionary registry root context after (.tail .refl finished_step) covered accessible
end Yulang.GeneralDictionaryJournalTreeExamples
