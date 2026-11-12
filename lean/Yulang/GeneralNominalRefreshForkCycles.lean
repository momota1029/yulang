import Yulang.GeneralNominalRefreshFork

/-! Both refresh outcomes have the same finite nominal argument chain.
Actual projection edges go from the outer list to the inner list to int;
the wider upper endpoint is top and supplies no nominal argument edge. -/
namespace Yulang.GeneralNominalRefreshForkCycles

open GeneralNominalRefreshFork
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)

private theorem int_not_nominal (name : Nat) (arguments : List Argument) :
    ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem inner_not_outer : ¬ Subtype (list (.base .int)) (list (list (.base .int))) := by
  intro below
  have same := (nominal_regular_invariant_exact _ _ _ _).mp below
  exact int_not_nominal 0 _ (same.2.2 0 _ _ rfl rfl).1

private theorem inner_source (source : Nat) (bound : source < 5)
    (equal : Equivalent (list (.base .int)) (model source).1) : source = 2 := by
  have cases : source = 0 ∨ source = 1 ∨ source = 2 ∨ source = 3 ∨ source = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (inner_not_outer equal.1)
  · exact False.elim (inner_not_outer equal.1)
  · rfl
  · exact False.elim (int_not_nominal 0 _ equal.2)
  · exact False.elim (GeneralNominalTopObservation.top_not_nominal 0 _ equal.2)

private theorem int_source (source : Nat) (bound : source < 5)
    (equal : Equivalent (.base .int) (model source).1) : source = 3 := by
  have cases : source = 0 ∨ source = 1 ∨ source = 2 ∨ source = 3 ∨ source = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (int_not_nominal 0 _ equal.1)
  · exact False.elim (int_not_nominal 0 _ equal.1)
  · exact False.elim (int_not_nominal 0 _ equal.1)
  · rfl
  · exact False.elim (GeneralNominalTopObservation.top_not_scalar .int equal.2)

private theorem projection_payload (source name index : Nat) (payload actual : Ty)
    (value : (model source).1 = list payload)
    (seen : GeneralNominalProjections.Observes model
      (.argument (.source source) name index) (.inl actual)) : Equivalent payload actual := by
  cases seen with
  | argument sourceSeen compared found =>
    cases sourceSeen
    rw [value] at compared
    have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
    have size := invariant.2.1
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
    have zero : index = 0 := by simp only [List.length_cons,List.length_nil] at size; omega
    subst index
    exact invariant.2.2 0 _ _ rfl found

theorem feedback_edge_forward (wide : Bool) (first last : Nat)
    (edge : GeneralNominalFeedbackK2.Edge (after wide) first last) : first < last := by
  have firstBound := source_bound (some wide) first edge.1
  have lastBound := source_bound (some wide) last edge.2.1
  rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_⟩,_,_⟩ | ⟨name,index,observed⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,equal⟩ := observed model (after_models wide)
    have cases : first = 0 ∨ first = 1 ∨ first = 2 ∨ first = 3 ∨ first = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · have payload := projection_payload 0 name index (list (.base .int)) actual rfl seen
      have target := inner_source last lastBound
        ⟨subtype_trans payload.1 equal.1,subtype_trans equal.2 payload.2⟩
      omega
    · have payload := projection_payload 1 name index (list (.base .int)) actual rfl seen
      have target := inner_source last lastBound
        ⟨subtype_trans payload.1 equal.1,subtype_trans equal.2 payload.2⟩
      omega
    · have payload := projection_payload 2 name index (.base .int) actual rfl seen
      have target := int_source last lastBound
        ⟨subtype_trans payload.1 equal.1,subtype_trans equal.2 payload.2⟩
      omega
    · cases seen with
      | argument sourceSeen compared found =>
        cases sourceSeen
        exact False.elim (int_not_nominal _ _ compared.1)
    · cases seen with
      | argument sourceSeen compared found =>
        cases sourceSeen
        exact False.elim (GeneralNominalTopObservation.top_not_nominal _ _ compared.1)

theorem feedback_path_forward (wide : Bool) (first last : Nat)
    (path : GeneralNominalFeedbackK2.Path (after wide) first last) : first ≤ last := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons edge _ ih => exact Nat.le_trans (Nat.le_of_lt (feedback_edge_forward wide _ _ edge)) ih

theorem feedback_acyclic (wide : Bool) (source : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle (after wide) source := by
  rintro ⟨next,edge,path⟩
  have forward := feedback_edge_forward wide source next edge
  have backward := feedback_path_forward wide next source path
  omega

theorem raw_edge_feedback (wide : Bool) (first last : Fin 5)
    (edge : GeneralNominalMixedRecurrence.Edge (state (some wide)) first last) :
    GeneralNominalFeedbackK2.Edge (after wide) first.val last.val := by
  refine ⟨?_,?_,?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨first,rfl⟩)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨last,rfl⟩)))
  · rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument (after wide) first last argument)

theorem raw_path_feedback (wide : Bool) (first last : Fin 5)
    (path : GeneralNominalMixedRecurrence.Path (state (some wide)) first last) :
    GeneralNominalFeedbackK2.Path (after wide) first.val last.val := by
  exact GeneralNominalMixedRecurrence.Path.rec
    (motive := fun first last _ => GeneralNominalFeedbackK2.Path (after wide) first.val last.val)
    (fun _ => .nil _) (fun edge _ ih => .cons (raw_edge_feedback wide _ _ edge) ih) path

theorem raw_acyclic (wide : Bool) (slot : Fin 5) :
    ¬ GeneralNominalCycleK2.RecursAt (state (some wide)) slot := by
  intro recurs
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurs
  exact feedback_acyclic wide slot.val
    ⟨next.val,raw_edge_feedback wide _ _ edge,raw_path_feedback wide _ _ path⟩

theorem legacy_not_recursive (wide : Bool) (slot : Fin 5) :
    ¬ GeneralNominalMixedRecurrence.RecursAt (state (some wide)) slot := by
  rintro ⟨⟨kind,_,_⟩,_⟩
  exact Fin.elim0 kind

theorem not_rootK2 (wide : Bool) (demand : Occurrence roles) :
    ¬ GeneralNominalFeedbackK2.RootK2 (after wide) demand := by
  rintro (⟨_,_,_,slot,_,recurs⟩ | ⟨_,_,_,cycle,_⟩)
  · exact raw_acyclic wide slot recurs
  · exact feedback_acyclic wide _ cycle

theorem not_candidateK2 (wide : Bool) (registry : GeneralDeclarations.Registry)
    (demand : Occurrence roles) : ¬ GeneralNominalFeedbackK2.CandidateK2 registry (after wide) demand := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact raw_acyclic wide visited.1 recurs
  · exact feedback_acyclic wide _ cycle

end Yulang.GeneralNominalRefreshForkCycles
