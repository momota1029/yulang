import Yulang.GeneralDeclarativeNestedFrame328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedResolve328
open GeneralDeclarativeNestedDecl328 (root impl reg interpret checked)
open GeneralDeclarativeNestedState328
open GeneralDeclarativeNestedProbe328
open GeneralDeclarativeNestedFrame328
open GeneralDeclarativeProjectedFrame326 (Rule sound)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Equation Models)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev branch (done : Nat → Prop) := Rule final reg interpret (support done) (tests done)
abbrev dict : Dictionary := .node impl.id [.node leaf.id []]

theorem root_only (d) (present : d ∈ reg.declarations) (role : d.role = root.role) : d = impl := by
  rcases List.mem_cons.mp present with rfl|tail
  · rfl
  · cases List.mem_singleton.mp tail
    cases role

theorem child_only (d) (present : d ∈ reg.declarations) (role : d.role = child.role) : d = leaf := by
  rcases List.mem_cons.mp present with rfl|tail
  · cases role
  · exact List.mem_singleton.mp tail

theorem selected_root (done : Nat → Prop) : branch done root (.selected impl.id [child]) := by
  refine .selected (parent_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_probe done⟩ ?_
    ⟨parentBase,placement,parent_frame done,child_exact⟩
  · rintro ⟨decl,⟨there,role⟩,blocked⟩
    cases root_only decl there role
    exact blocked (root_probe done)
  · rintro decl ⟨⟨there,role⟩,_⟩
    rw [root_only decl there role]

theorem selected_child (done : Nat → Prop) : branch done child (.selected leaf.id []) := by
  refine .selected (child_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_probe done⟩ ?_
    ⟨leafBase,placement,child_frame done,rfl⟩
  · rintro ⟨decl,⟨there,role⟩,blocked⟩
    cases child_only decl there role
    exact blocked (child_probe done)
  · rintro decl ⟨⟨there,role⟩,_⟩
    rw [child_only decl there role]

theorem selected (done : Nat → Prop) : Classify (branch done) root (.selected dict) :=
  ⟨.selected impl.id [.selected leaf.id []],
    .selected (selected_root done) (.cons (.selected (selected_child done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem declared : Declared reg root := by
  intro output here
  cases List.mem_singleton.mp here
  exact ⟨none,rfl⟩

theorem certified (m) (fits : Models final m) : Evidence reg interpret m root dict :=
  sound checked declared fits (selected (fun _ => False))

end Yulang.GeneralDeclarativeNestedResolve328
