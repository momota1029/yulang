import Yulang.GeneralDeclarativeCompoundFrame325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundResolve325
open GeneralDeclarativeCompoundDecl325
open GeneralDeclarativeCompoundState325
open GeneralDeclarativeCompoundProbe325
open GeneralDeclarativeCompoundFrame325
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeSourceSelection325 (Rule sound actual_local_compiler)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev dict : Dictionary := .node impl.id [.node leaf.id []]
abbrev branch (done : Nat → Prop) := Rule final reg interpret (support2 done) (tests done)

theorem parent_only (d) (registered : d ∈ reg.declarations) (role : d.role = demand.role) : d = impl := by
  rcases List.mem_cons.mp registered with rfl|late
  · rfl
  · cases List.mem_singleton.mp late
    cases role

theorem child_only (d) (registered : d ∈ reg.declarations) (role : d.role = call.role) : d = leaf := by
  rcases List.mem_cons.mp registered with rfl|late
  · cases role
  · exact List.mem_singleton.mp late

theorem selected_parent (done : Nat → Prop) : branch done demand (.selected impl.id [call]) := by
  refine .selected (root_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_probe done⟩ ?_
    ⟨parentBase,placement,root_recorded done,exact_emitted⟩
  · rintro ⟨d,⟨registered,role⟩,blocked⟩
    cases parent_only d registered role
    exact blocked (root_probe done)
  · rintro d ⟨⟨registered,role⟩,_⟩
    rw [parent_only d registered role]

theorem selected_child (done : Nat → Prop) : branch done call (.selected leaf.id []) := by
  refine .selected (child_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_probe done⟩ ?_
    ⟨childBase,placement,child_recorded done,rfl⟩
  · rintro ⟨d,⟨registered,role⟩,blocked⟩
    cases child_only d registered role
    exact blocked (child_probe done)
  · rintro d ⟨⟨registered,role⟩,_⟩
    rw [child_only d registered role]

theorem classifies (done : Nat → Prop) : Classify (branch done) demand (.selected dict) :=
  ⟨.selected impl.id [.selected leaf.id []],
    .selected (selected_parent done) (.cons (.selected (selected_child done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem declared : Declared reg demand := by
  intro out there
  cases List.mem_singleton.mp there
  exact ⟨none,rfl⟩

theorem every_model (m) (valid : Models final m) : Evidence reg interpret m demand dict :=
  sound checked declared valid (classifies (fun _ => False))

theorem genuine_compound :
    ¬ (∃ rhs, (⟨1,rhs⟩ : Equation) ∈ final.equations) ∧
    call.arguments = [⟨8,9,10⟩] ∧ Classify (branch (fun _ => False)) demand (.selected dict) ∧
    ∃ m, Models final m ∧ Evidence reg interpret m demand dict :=
  ⟨absence_of_center_row,rfl,classifies _,assign true,inhabited,every_model _ inhabited⟩

end Yulang.GeneralDeclarativeCompoundResolve325
