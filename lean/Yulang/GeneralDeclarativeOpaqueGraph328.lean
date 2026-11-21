import Yulang.GeneralDeclarativeOpaqueAuthority328
import Yulang.GeneralDeclarativeK2Mono324
import Yulang.GeneralDeclarativeInspect321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueGraph328
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOpaqueNames328 (first second row expose)
open GeneralDeclarativeOpaqueAuthority328 (FreshName outside not_root fresh_alias unchanged_alias)
open GeneralDeclarativeCopyCollapse326 (ordinary_eq_names)
open GeneralDeclarativeK2Graph321 (View Descends Path Shape aliasView)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeLowerKnown321 (Alias alias_symm)

theorem fresh_is_terminal {s : State} (name : FreshName s root extra n) :
    ¬structural (expose s root extra) n shape := by
  rintro ⟨owner,linked,exp,found,constr⟩
  have same := fresh_alias name linked
  subst owner
  rcases List.mem_append.mp found with old|added
  · exact outside name (ordinary_eq_names _ old List.mem_cons_self)
  · have equal := congrArg Equation.left (List.mem_singleton.mp added)
    exact not_root name equal

theorem before_or_fresh {s : State}
    (seen : structural (expose s root extra) n shape) :
    structural s n shape ∨ shape = .primitive .pair [first s root extra,second s root extra] := by
  obtain ⟨owner,linked,code,found,reading⟩ := seen
  rcases List.mem_append.mp found with before|new
  · exact .inl ⟨owner,(unchanged_alias root extra).mp linked,code,before,reading⟩
  · have delta := congrArg Equation.right (List.mem_singleton.mp new)
    change code = (row s root extra).right at delta
    rw [delta] at reading
    exact .inr (Option.some.inj reading).symm

theorem edge {s : State}
    (seen : Descends (structural (expose s root extra)) a b) :
    Descends (structural s) a b ∨ FreshName s root extra b := by
  obtain ⟨shape,looked,child⟩ := seen
  rcases before_or_fresh looked with rewritten|pair
  · exact .inl ⟨shape,rewritten,child⟩
  · subst shape
    exact .inr (by simpa [Shape.children,FreshName] using child)

theorem path_from_fresh {s : State}
    (fresh : FreshName s root extra a) (p : Path (structural (expose s root extra)) a b) : a = b := by
  cases p with
  | refl => rfl
  | next one rest =>
    obtain ⟨shape,direct,child⟩ := one
    exact False.elim (fresh_is_terminal fresh direct)

theorem past_path {s : State}
    (p : Path (structural (expose s root extra)) a b) (notFresh : ¬FreshName s root extra b) :
    Path (structural s) a b := by
  induction p with
  | refl n => exact .refl _
  | next first rest ih =>
    rcases edge first with old|new
    · exact .next old (ih notFresh)
    · exact False.elim (notFresh (path_from_fresh new rest ▸ new))

/-- Merely writing a pair of entirely new logical leaves adds no
ordinary K2 finding. This theorem is for the pair equation alone;
additional projected bounds can require a separate graph argument. -/
theorem cycles {s : State} (root : Nat) (extra : List Nat) (atName : Nat) :
    AliasCycle (expose s root extra) (observed (expose s root extra)) atName ↔
      AliasCycle s (observed s) atName := by
  constructor
  · rintro ⟨next,last,first,tail,returns⟩
    have noStart : ¬FreshName s root extra atName := by
      intro new
      obtain ⟨_,positive,_⟩ := first
      exact fresh_is_terminal new positive
    have noEnd : ¬FreshName s root extra last := by
      intro new
      exact noStart (fresh_alias new returns ▸ new)
    rcases edge first with before|new
    · exact ⟨next,last,before,past_path tail noEnd,(unchanged_alias root extra).mp returns⟩
    · exact False.elim (noEnd (path_from_fresh new tail ▸ new))
  · exact GeneralDeclarativeK2Mono324.preserve (s := s) (t := expose s root extra) rfl
      (fun _ h => List.mem_append_left _ h)

end Yulang.GeneralDeclarativeOpaqueGraph328
