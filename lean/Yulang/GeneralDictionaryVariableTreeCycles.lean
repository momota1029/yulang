import Yulang.GeneralDictionaryVariableTreeInitialJoint

namespace Yulang.GeneralDictionaryVariableTreeCycles
open GeneralDictionaryVariableTreeExample
open GeneralNominalBranchExample (state context root model)
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier
open GeneralNominalSaturationState

theorem edge_shape (first last : Nat)
    (edge : GeneralNominalFeedbackK2.Edge start.current first last) : first = 0 ∧ last ≠ 0 := by
  rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_,_⟩,_,_⟩ | ⟨name,index,observed⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,equal⟩ := observed model initial_models
    cases seen with
    | argument source compared found =>
      cases source
      rename_i args
      have firstZero : first = 0 := by
        apply Classical.byContradiction
        intro nonzero
        have bound := (List.getElem?_eq_some_iff.mp found).1
        by_cases one : first = 1
        · have le : Subtype (nominal 2 []) (nominal name args) := by simpa [GeneralNominalBranchExample.model,nonzero,one] using compared.1
          have length := (nominal_regular_invariant_exact _ _ _ _).mp le |>.2.1
          simp only [List.length_nil] at length
          omega
        · have le : Subtype (nominal 3 []) (nominal name args) := by simpa [GeneralNominalBranchExample.model,nonzero,one] using compared.1
          have length := (nominal_regular_invariant_exact _ _ _ _).mp le |>.2.1
          simp only [List.length_nil] at length
          omega
      subst first
      have parentLe : Subtype (nominal 5 [.inl (nominal 2 []),.inl (nominal 3 [])]) (nominal name args) := compared.1
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp parentLe
      have length := invariant.2.1
      have bound := (List.getElem?_eq_some_iff.mp found).1
      have cases : index = 0 ∨ index = 1 := by simp only [List.length_cons,List.length_nil] at length; omega
      refine ⟨rfl,?_⟩
      intro zero
      subst last
      rcases cases with rfl | rfl
      · have child := invariant.2.2 0 (.inl (nominal 2 [])) (.inl actual) rfl found
        have clash := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans child.1 equal.1)
        cases clash.1
      · have child := invariant.2.2 1 (.inl (nominal 3 [])) (.inl actual) rfl found
        have clash := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans child.1 equal.1)
        cases clash.1

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.current source := by
  rintro ⟨next,edge,path⟩
  have shape := edge_shape source next edge
  cases path with
  | nil => exact shape.2 shape.1
  | cons nextEdge rest => exact shape.2 (edge_shape _ _ nextEdge).1

private theorem old_edge (first last : Fin 3) (edge : GeneralNominalMixedRecurrence.Edge state first last) :
    GeneralNominalFeedbackK2.Edge start.current first.val last.val := by
  refine ⟨?_,?_,?_⟩
  · simp [start,GeneralNominalSupport.initial,initial,GeneralNominalState.sources,List.ofFn_succ]; omega
  · simp [start,GeneralNominalSupport.initial,initial,GeneralNominalState.sources,List.ofFn_succ]; omega
  · rcases edge with ⟨kind,_,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument start.current first last argument)

private theorem old_path (first last : Fin 3) (path : GeneralNominalMixedRecurrence.Path state first last) :
    GeneralNominalFeedbackK2.Path start.current first.val last.val := by
  exact GeneralNominalMixedRecurrence.Path.rec
    (motive := fun first last _ => GeneralNominalFeedbackK2.Path start.current first.val last.val)
    (fun _ => .nil _) (fun edge _ ih => .cons (old_edge _ _ edge) ih) path

theorem old_acyclic (slot : Fin 3) : ¬ GeneralNominalCycleK2.RecursAt state slot := by
  intro recurrent
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurrent
  exact acyclic slot.val ⟨next.val,old_edge _ _ edge,old_path _ _ path⟩
end Yulang.GeneralDictionaryVariableTreeCycles
