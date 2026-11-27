import Yulang.GeneralDeclarativeI65I74ProjectionCut464
import Yulang.GeneralDeclarativeI65I74SplitEscapeFinite446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (State Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open Yulang.GeneralDeclarativeI65.I72
open List410 (ExactEscapeWire)
open SplitEscape446 (SplitReady splitCheck446 split_check_reflects_actual_rows446
  raw_safe_iff_finite_split_witness446)

theorem checking_a_supplied_projection_cut_is_exact_extended_split
    {s : State} {site : Nat} {term : Expr} {form : Shape}
    (shape : shapeOf term = some form) (w : ExactEscapeWire) :
    checksNamedProjectionCut s site term w = true ↔
      splitCheck446 (extendedRows s ⟨site,term⟩) site w = true := by
  let r : Equation := ⟨site,term⟩
  have noAlias : ∀ n, term ≠ .variable n := by
    intro n claimed
    rw [claimed] at shape
    cases shape
  unfold checksNamedProjectionCut
  simp only [shape,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
    split_check_reflects_actual_rows446]
  constructor
  · rintro ⟨before,children⟩
    refine ⟨before.boundShape,?_,before.rootZero,?_⟩
    · intro e seen n flat
      change _ ∈ s.equations ++ [r] at seen
      rcases List.mem_append.mp seen with old|new
      · exact before.flatSide e old n flat
      · have eq := List.mem_singleton.mp new
        subst e
        exact (noAlias n flat).elim
    · intro e seen h parsed active n there
      change _ ∈ s.equations ++ [r] at seen
      rcases List.mem_append.mp seen with old|new
      · exact before.edges e old h parsed active n there
      · have eq := List.mem_singleton.mp new
        subst e
        have same := Option.some.inj (shape.symm.trans parsed)
        subst h
        exact children n there
  · intro after
    refine ⟨⟨after.boundShape,?_,after.rootZero,?_⟩,?_⟩
    · intro e seen n flat
      exact after.flatSide e (List.mem_append_left _ seen) n flat
    · intro e seen h parsed active n there
      exact after.edges e (List.mem_append_left _ seen) h parsed active n there
    · intro n there
      exact after.edges r (List.mem_append_right _ List.mem_cons_self) form shape
        (by change w.side site ≤ 1; rw [after.rootZero]; decide) n there

private theorem into_after {s : State} {r : Equation}
    (same : ∀ a b, Alias (extendedRows s r) a b ↔ Alias s a b)
    {x y : Nat} (walk : Path (structural s) x y) :
    Path (structural (extendedRows s r)) x y := by
  induction walk with
  | refl => exact .refl _
  | next d _ ih =>
    obtain ⟨h,⟨owner,link,e,seen,parsed⟩,selected⟩ := d
    exact .next ⟨h,⟨owner,(same _ _).mpr link,e,List.mem_append_left _ seen,parsed⟩,selected⟩ ih

theorem physical_new_row_root_cycle_exactly_old_or_old_return_from_child
    {s : State} {site : Nat} {term : Expr} {form : Shape} (shape : shapeOf term = some form) :
    AliasCycle (extendedRows s ⟨site,term⟩) (observed (extendedRows s ⟨site,term⟩)) site ↔
      AliasCycle s (observed s) site ∨
        ∃ child ∈ form.children, ∃ last, Alias s last site ∧ Path (structural s) child last := by
  let r : Equation := ⟨site,term⟩
  have noAlias : ∀ n, term ≠ .variable n := by
    intro n claimed
    rw [claimed] at shape
    cases shape
  have added := actually_appending_nonalias_row_changes_shapes_only_on_old_alias_class s site term noAlias
  have fromNew {src child} (edge : Descends (structural (extendedRows s r)) src child)
      (notOld : ¬ Descends (structural s) src child) :
      child ∈ form.children := by
    obtain ⟨h,⟨a,al,e,seen,parsed⟩,used⟩ := edge
    change _ ∈ s.equations ++ [r] at seen
    rcases List.mem_append.mp seen with original|new
    · exact (notOld ⟨h,⟨a,(added.aliases src a).mp al,e,original,parsed⟩,used⟩).elim
    · have eq : e=term := congrArg Equation.right (List.mem_singleton.mp new)
      subst e
      have he := Option.some.inj (shape.symm.trans parsed)
      subst h
      exact used
  constructor
  · rintro ⟨initial,last,first,rest,final⟩
    have final' := (added.aliases last site).mp final
    by_cases old : Descends (structural s) site initial
    · rcases (some_new_shape_path_through_alias_class_has_one_exact_new_edge added).mp rest with
        before | ⟨a,b,_,_,fresh,notOld,tail⟩
      · exact .inl ⟨initial,last,old,before,final'⟩
      · exact .inr ⟨b,fromNew fresh notOld,last,final',tail⟩
    · have child := fromNew first old
      rcases (some_new_shape_path_through_alias_class_has_one_exact_new_edge added).mp rest with
        before | ⟨a,_,leading,belongs,_,_,_⟩
      · exact .inr ⟨initial,child,last,final',before⟩
      · exact .inr ⟨initial,child,a,belongs,leading⟩
  · rintro (⟨c,last,⟨h,first,used⟩,tail,al⟩ | ⟨child,used,last,al,tail⟩)
    · exact ⟨c,last,⟨h,added.keep _ _ first,used⟩,into_after added.aliases tail,
        (added.aliases last site).mpr al⟩
    · have atRow : r ∈ (extendedRows s r).equations := List.mem_append_right _ List.mem_cons_self
      have extra : Descends (structural (extendedRows s r)) site child :=
        ⟨form,⟨site,alias_refl _,term,atRow,shape⟩,used⟩
      exact ⟨child,last,extra,into_after added.aliases tail,(added.aliases last site).mpr al⟩

/-- The finite certificate exists exactly for a proposed actual shape whose
new children cannot return to the original alias class and whose source
was already safe. Placement/issuer and equation entailment remain separate. -/
theorem original_projection_cut_has_finite_wire_exactly_when_safe
    {s : State} {site : Nat} {term : Expr} {form : Shape} (shape : shapeOf term = some form) :
    (∃ w, checksNamedProjectionCut s site term w = true) ↔
      (¬ AliasCycle s (observed s) site) ∧
      ∀ child ∈ form.children, ∀ last, Alias s last site → ¬ Path (structural s) child last := by
  have existEquiv : (∃ w, checksNamedProjectionCut s site term w = true) ↔
      ∃ w, splitCheck446 (extendedRows s ⟨site,term⟩) site w = true :=
    exists_congr (checking_a_supplied_projection_cut_is_exact_extended_split shape)
  rw [existEquiv,←raw_safe_iff_finite_split_witness446,
    physical_new_row_root_cycle_exactly_old_or_old_return_from_child shape,not_or]
  constructor
  · rintro ⟨first,no⟩
    exact ⟨first,fun x member y alias tail => no ⟨x,member,y,alias,tail⟩⟩
  · rintro ⟨first,no⟩
    exact ⟨first,fun ⟨x,member,y,alias,tail⟩ => no x member y alias tail⟩

end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
