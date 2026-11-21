import Yulang.GeneralDeclarativeCopyCollapse326
import Yulang.GeneralDeclarativeK2Mono324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCopyK2326
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAuthorizedCopy326 (name writing extended)
open GeneralDeclarativeCopyCollapse326 (collapse base_unchanged copy_collapses ordinary_eq_names alias)
open GeneralDeclarativeK2Alias321 (AliasCycle alias_cycle_iff)
open GeneralDeclarativeK2Graph321 (View Shape Descends Path aliasView)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeGraphFootprint326 (shape_children)
open GeneralDeclarativeLowerKnown321 (Alias)

theorem ordinary_shape {s : State} (source : Nat) (keep : List Nat)
    (seen : observed (extended s source keep) n head) :
    ∃ exp, (⟨n,exp⟩ : Equation) ∈ s.equations ∧ shapeOf exp = some head := by
  rcases seen with ⟨exp,written,shown⟩
  rcases List.mem_append.mp written with retained|added
  · exact ⟨exp,retained,shown⟩
  · have same := congrArg Equation.right (List.mem_singleton.mp added)
    change exp = .variable source at same
    subst exp
    cases shown

theorem edge {s : State} (source : Nat) (keep : List Nat)
    (later : Descends (aliasView (extended s source keep) (observed (extended s source keep))) a b) :
    Descends (aliasView s (observed s)) (collapse s source keep a) (collapse s source keep b) := by
  obtain ⟨head,⟨owner,route,shape⟩,child⟩ := later
  obtain ⟨exp,prior,formed⟩ := ordinary_shape source keep shape
  have names := ordinary_eq_names _ prior
  have linked := alias source keep route
  rw [base_unchanged source keep (names List.mem_cons_self)] at linked
  have childOriginal := names (List.mem_cons_of_mem _ (shape_children formed child))
  rw [base_unchanged source keep childOriginal]
  exact ⟨head,⟨owner,linked,exp,prior,formed⟩,child⟩

theorem path {s : State} (source : Nat) (keep : List Nat)
    (later : Path (aliasView (extended s source keep) (observed (extended s source keep))) a b) :
    Path (aliasView s (observed s)) (collapse s source keep a) (collapse s source keep b) := by
  induction later with
  | refl n => exact .refl _
  | next down _ rest => exact .next (edge source keep down) rest

/-- Fresh ordinary name reuse alone neither creates nor erases K2
cycles. At the new alias, the criterion is exactly the criterion at
its source; at every old name, it is the old criterion. -/
theorem exact {s : State} (source : Nat) (keep : List Nat) (root : Nat) :
    AliasCycle (extended s source keep) (observed (extended s source keep)) root ↔
      AliasCycle s (observed s) (collapse s source keep root) := by
  constructor
  · rintro ⟨first,last,a,b,c⟩
    exact ⟨_,_,edge source keep a,path source keep b,alias source keep c⟩
  · intro before
    have grows : s.equations ⊆ (extended s source keep).equations :=
      fun _ old => List.mem_append_left _ old
    have restored := GeneralDeclarativeK2Mono324.preserve (s := s) (t := extended s source keep) rfl grows before
    by_cases fresh : root = name s source keep
    · subst root
      rw [copy_collapses] at restored
      have copied : Alias (extended s source keep) (name s source keep) source :=
        .forward (List.mem_append_right _ List.mem_cons_self)
      exact (alias_cycle_iff copied).mpr restored
    · simpa [collapse,fresh] using restored

end Yulang.GeneralDeclarativeCopyK2326
