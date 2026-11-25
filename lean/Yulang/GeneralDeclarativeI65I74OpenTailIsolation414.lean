import Yulang.GeneralDeclarativeI65I74OpenTailPriority414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf fields)
open GeneralDeclarativeK2Graph321 (Shape Descends)
open GeneralDeclarativeK2Alias321 (AliasCycle)

theorem bounds_on_exact_input_are_reflexive414 {s q} (a : OpenInput s q)
    {x y} (path : Bound s.core.current.ordinary.normal x y) : x = y := by
  induction path with
  | interval member => rw [a.noBounds] at member; cases member
  | constraint member => rw [a.noAtoms] at member; cases member
  | refl => rfl
  | trans _ _ up down => exact up.trans down

theorem aliases_on_exact_input_are_reflexive414 {s q} (a : OpenInput s q)
    {x y} (path : GeneralDeclarativeLowerKnown321.Alias s.core.current.ordinary x y) : x = y := by
  have noNameRow : ∀ v w,
      (⟨v,.variable w⟩ : GeneralDeclarativeHead320.Equation) ∉ s.core.current.ordinary.equations := by
    intro v w yes
    rw [a.exactRows] at yes
    simp [openRow,intRow] at yes
  induction path with
  | bounds up _ => exact bounds_on_exact_input_are_reflexive414 a up
  | forward link => exact (noNameRow _ _ link).elim
  | backward link => exact (noNameRow _ _ link).elim
  | trans _ _ earlier later => exact earlier.trans later

theorem no_aliased_row_for_actual_tail414 {s q} (a : OpenInput s q) {x}
    (alias : GeneralDeclarativeLowerKnown321.Alias s.core.current.ordinary a.tail x) :
    ∀ e ∈ s.core.current.ordinary.equations, e.left ≠ x := by
  cases aliases_on_exact_input_are_reflexive414 a alias
  exact no_row_for_actual_tail414 a

theorem no_raw_structural_step_in_exact_open_input414 {s q} (a : OpenInput s q) (x y : Nat) :
    ¬ Descends (structural s.core.current.ordinary) x y := by
  rintro ⟨h,⟨v,_,raw,hEq,asShape⟩,child⟩
  rw [a.exactRows] at hEq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hEq
  rcases hEq with matchRecord|matchInt
  · cases GeneralDeclarativeHead320.Equation.mk.inj matchRecord with
    | intro _ expr => rw [expr] at asShape; simp [shapeOf,fields] at asShape
  · cases GeneralDeclarativeHead320.Equation.mk.inj matchInt with
    | intro _ expr =>
      rw [expr] at asShape
      have scalar : .primitive (.scalar .int) [] = h := Option.some.inj asShape
      cases scalar
      simp [Shape.children] at child

theorem exact_open_input_all_positions_raw_safe414 {s q} (a : OpenInput s q) (x : Nat) :
    ¬ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) x := by
  rintro ⟨y,_,first,_,_⟩
  exact no_raw_structural_step_in_exact_open_input414 a x y first

/-- Make the two actual open-source links explicit, independently of the
normalized graph's inability to materialize an open record row. -/
def SourceProjection {s q} (a : OpenInput s q) : Nat → Nat → Prop :=
  fun x y => x = a.root ∧ (y = a.field ∨ y = a.tail)

inductive SourcePath {s q} (a : OpenInput s q) : Nat → Nat → Prop where
  | refl (x : Nat) : SourcePath a x x
  | next : SourceProjection a x y → SourcePath a y z → SourcePath a x z

theorem open_source_links_do_not_close414 {s q} (a : OpenInput s q) {x y}
    (one : SourceProjection a x y) : ¬ SourcePath a y x := by
  intro rest
  have different : y ≠ a.root := by
    rcases one.2 with f|t
    · exact f ▸ (Ne.symm a.rootField)
    · exact t ▸ (Ne.symm a.rootTail)
  cases rest with
  | refl => exact different one.1
  | next edge _ => exact different edge.1

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
