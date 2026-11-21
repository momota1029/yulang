import Yulang.GeneralDeclarativeRecordFrame326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordResolve326
open GeneralDeclarativeRecordDecl326
open GeneralDeclarativeRecordState326
open GeneralDeclarativeRecordProbe326
open GeneralDeclarativeRecordFrame326
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeProjectedFrame326 (Rule sound)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev branch (done : Nat → Prop) := Rule final registry interpretation (support2 done) (tests done)
abbrev dictionary : Dictionary := .node decl.id [.node leaf.id []]

theorem root_only (d) (inRegistry : d ∈ registry.declarations) (role : d.role = root.role) : d = decl := by
  rcases List.mem_cons.mp inRegistry with rfl|tail
  · rfl
  · cases List.mem_singleton.mp tail
    cases role

theorem child_only (d) (inRegistry : d ∈ registry.declarations) (role : d.role = child.role) : d = leaf := by
  rcases List.mem_cons.mp inRegistry with rfl|tail
  · cases role
  · exact List.mem_singleton.mp tail

theorem root_selected (done : Nat → Prop) : branch done root (.selected decl.id [child]) := by
  refine .selected (ready_root done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,head_root done⟩ ?_
    ⟨base,place,root_frame done,generated_child⟩
  · rintro ⟨candidate,⟨registered,role⟩,pending⟩
    cases root_only candidate registered role
    exact pending (head_root done)
  · rintro candidate ⟨⟨registered,role⟩,_⟩
    rw [root_only candidate registered role]

theorem child_selected (done : Nat → Prop) : branch done child (.selected leaf.id []) := by
  refine .selected (ready_child done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,head_child done⟩ ?_
    ⟨childBase,place,child_frame done,rfl⟩
  · rintro ⟨candidate,⟨registered,role⟩,pending⟩
    cases child_only candidate registered role
    exact pending (head_child done)
  · rintro candidate ⟨⟨registered,role⟩,_⟩
    rw [child_only candidate registered role]

theorem declared : Declared registry root := by
  intro req named
  cases List.mem_singleton.mp named
  exact ⟨none,rfl⟩

theorem whole_selected (done : Nat → Prop) : Classify (branch done) root (.selected dictionary) :=
  ⟨.selected decl.id [.selected leaf.id []],
    .selected (root_selected done) (.cons (.selected (child_selected done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem all_model (m) (valid : Models final m) : Evidence registry interpretation m root dictionary :=
  sound checked declared valid (whole_selected (fun _ => False))

/-- A checked source head takes its actual tail from a closed visible
record. A shadowed self name is not a visible K2 edge. The real child
uses the payload, while the actual tail determines the root output. -/
theorem exact_closed_tail :
    GeneralDeclarativeGraphRows321.fields (GeneralDeclarativeRecordK2326.row rawNames) =
      some [(7,3),(8,4)] ∧
    Classify (branch (fun _ => False)) root (.selected dictionary) ∧
    ∃ m, Models final m ∧ Evidence registry interpretation m root dictionary :=
  ⟨exact_labels,whole_selected _,model,populated,all_model _ populated⟩

end Yulang.GeneralDeclarativeRecordResolve326
