import Yulang.GeneralNominalCycleReadback

/-! The finite set of all selected where descendants is derived recursively
from Checked and the explicit readback correspondence. No support list, depth
limit or finite-basis certificate is an input. This is for a fixed snapshot;
shared-state updates still need a correspondence across refinements. -/
namespace Yulang.GeneralNominalCycleSupport

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCycleK2
open GeneralNominalCycleReadback

variable {roles : Roles.RoleDecls} {registry : Registry} {context : GeneralNominalCandidates.Context}

noncomputable def frontier (checked : Checked registry) (root : Occurrence roles) :
    CommonRoleOutermostResolver.Frontier (Occurrence roles) := Classical.choose (local_total registry checked context root)

theorem frontier_local (checked : Checked registry) (root : Occurrence roles) :
    Local registry context root (frontier (context := context) checked root) :=
  Classical.choose_spec (local_total registry checked context root)

noncomputable def children (checked : Checked registry) (root : Occurrence roles) : List (Occurrence roles) :=
  match frontier (context := context) checked root with | .selected _ children => children | _ => []

theorem children_exact (checked : Checked registry) (root child : Occurrence roles) :
    child ∈ children (context := context) checked root ↔
      CommonRoleOutermostResolver.Child (Local registry context) child root := by
  have localRule := frontier_local (context := context) checked root
  constructor
  · intro member
    unfold children at member
    cases result : frontier (context := context) checked root with
    | pending => simp [result] at member
    | rejected => simp [result] at member
    | ambiguous => simp [result] at member
    | selected key cs =>
      rw [result] at localRule
      refine ⟨key,cs,localRule,?_⟩
      change child ∈ cs
      simpa [result] using member
  · rintro ⟨key,cs,selected,member⟩
    have same := local_functional localRule selected
    unfold children
    rw [same]
    exact member

noncomputable def support (checked : Checked registry) (readback : Readback roles registry context)
    (root : Occurrence roles) : List (Occurrence roles) :=
  root :: (children (context := context) checked root).attach.flatMap (fun child => support checked readback child.val)
termination_by weight readback root
decreasing_by exact child_decreases checked readback root child.val ((children_exact checked root child.val).mp child.property)

theorem root_mem_support (checked : Checked registry) (readback : Readback roles registry context) (root : Occurrence roles) :
    root ∈ support checked readback root := by
  rw [support]; exact List.mem_cons_self

theorem child_support_subset (checked : Checked registry) (readback : Readback roles registry context)
    (parent child : Occurrence roles) (edge : CommonRoleOutermostResolver.Child (Local registry context) child parent) :
    support checked readback child ⊆ support checked readback parent := by
  intro target member
  rw [support]
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  have childMember := (children_exact checked parent child).mpr edge
  exact ⟨⟨child,childMember⟩,List.mem_attach _ _,member⟩

inductive Reaches (registry : Registry) (context : GeneralNominalCandidates.Context) :
    Occurrence roles → Occurrence roles → Prop
  | refl (root) : Reaches registry context root root
  | cons : CommonRoleOutermostResolver.Child (Local registry context) child parent →
      Reaches registry context child last → Reaches registry context parent last

theorem reached_in_support (checked : Checked registry) (readback : Readback roles registry context)
    (path : Reaches registry context root child) : child ∈ support checked readback root := by
  induction path with
  | refl root => exact root_mem_support checked readback root
  | cons edge _ ih => exact child_support_subset checked readback _ _ edge ih

theorem support_reached (checked : Checked registry) (readback : Readback roles registry context)
    (root child : Occurrence roles) (member : child ∈ support checked readback root) : Reaches registry context root child := by
  induction root using (measure (weight readback)).wf.induction with
  | h root ih =>
    rw [support] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact .refl _
    · obtain ⟨next,_,member⟩ := List.mem_flatMap.mp member
      have edge := (children_exact checked root next.val).mp next.property
      exact .cons edge (ih next.val (child_decreases checked readback root next.val edge) member)

theorem finite_descendants (checked : Checked registry) (readback : Readback roles registry context)
    (root : Occurrence roles) :
    ∃ demands : List (Occurrence roles), ∀ child, child ∈ demands ↔ Reaches registry context root child :=
  ⟨support checked readback root,fun child =>
    ⟨support_reached checked readback root child,reached_in_support checked readback⟩⟩

end Yulang.GeneralNominalCycleSupport
