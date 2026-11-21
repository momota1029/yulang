import Yulang.GeneralDeclarativeNamedAliasProbe325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNamedAliasResolve325
open GeneralDeclarativeHiddenWhere324 (root child parent implementation registry checked clause named rhs place)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation empty normCode normal_compiles)
open GeneralDeclarativeHiddenState324 (direct)
open GeneralDeclarativeHiddenProbe324 (root_bounds)
open GeneralDeclarativeNamedAliasState325
open GeneralDeclarativeNamedAliasProbe325
open GeneralDeclarativeExampleSource320 (point)
open GeneralDeclarativeFrameReadback325 (Frame sourceNames)
open GeneralDeclarativeDerivedSource325 (Current Rule sound)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev base (_ : Nat) : GeneralDeclarativeWhere319.Capture := point 3
abbrev dict : Dictionary := .node parent.id [.node implementation.id []]

theorem actual_child : children parent (sourceNames parent place base) place = [child] := rfl

theorem root_frame (done : Nat → Prop) :
    Frame ordinary registry interpretation (sources done) root parent base place := by
  refine ⟨.cons ⟨root_bounds _ 0,.actual normal_compiles (head_trace done .actual) ?_⟩ .nil,
    fun _ _ => root_bounds _ 3,?_⟩
  · intro o there
    cases List.mem_singleton.mp there
    exact .refl _
  · intro clause seen
    cases List.mem_singleton.mp seen
    refine ⟨⟨[.variable 0],rfl,?_⟩,?_⟩
    · intro pos pat term hp _ compound
      cases List.mem_singleton.mp (List.mem_of_getElem? hp)
      exact False.elim (compound 0 rfl)
    · intro row seen
      cases List.mem_singleton.mp seen
      exact ⟨normCode,rfl,fun _ => named_where_alias⟩

theorem child_frame (done : Nat → Prop) :
    Frame ordinary registry interpretation (sources done) child implementation base place := by
  refine ⟨.cons ⟨root_bounds _ 3,.actual rfl .capture ?_⟩ .nil,
    fun _ _ => root_bounds _ 3,fun _ h => False.elim (List.not_mem_nil h)⟩
  intro o inTrace
  cases List.mem_singleton.mp inTrace
  exact .refl _

theorem current_root (done : Nat → Prop) :
    Current ordinary registry interpretation (sources done) root parent base place :=
  ⟨root_frame done,[rootOut],rfl,fun _ seen => by
    cases List.mem_singleton.mp seen
    exact parent_derived⟩

theorem current_child (done : Nat → Prop) :
    Current ordinary registry interpretation (sources done) child implementation base place :=
  ⟨child_frame done,[childOut],rfl,fun _ seen => by
    cases List.mem_singleton.mp seen
    exact child_derived⟩

theorem root_only (impl) (visible : impl ∈ registry.declarations) (role : impl.role = root.role) :
    impl = parent := by
  rcases List.mem_cons.mp visible with rfl|inside
  · rfl
  · cases List.mem_singleton.mp inside
    cases role

theorem child_only (impl) (visible : impl ∈ registry.declarations) (role : impl.role = child.role) :
    impl = implementation := by
  rcases List.mem_cons.mp visible with rfl|inside
  · cases role
  · exact List.mem_singleton.mp inside

abbrev branch (done : Nat → Prop) := Rule ordinary registry interpretation (sources done) (tests done)

theorem chosen_root (done : Nat → Prop) : branch done root (.selected parent.id [child]) := by
  refine .selected (root_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_probe done⟩ ?_
    ⟨base,place,current_root done,actual_child⟩
  · rintro ⟨impl,⟨visible,role⟩,unknown⟩
    cases root_only impl visible role
    exact unknown (root_probe done)
  · rintro impl ⟨⟨visible,role⟩,_⟩
    rw [root_only impl visible role]

theorem chosen_child (done : Nat → Prop) : branch done child (.selected implementation.id []) := by
  refine .selected (child_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_probe done⟩ ?_
    ⟨base,place,current_child done,rfl⟩
  · rintro ⟨impl,⟨visible,role⟩,unknown⟩
    cases child_only impl visible role
    exact unknown (child_probe done)
  · rintro impl ⟨⟨visible,role⟩,_⟩
    rw [child_only impl visible role]

theorem chosen (done : Nat → Prop) : Classify (branch done) root (.selected dict) :=
  ⟨.selected parent.id [.selected implementation.id []],
    .selected (chosen_root done) (.cons (.selected (chosen_child done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem declared : Declared registry root := by
  intro out found
  cases List.mem_singleton.mp found
  exact ⟨none,rfl⟩

theorem every_model (m) (valid : Models ordinary m) :
    Evidence registry interpretation m root dict :=
  sound checked declared valid (chosen (fun _ => False))

theorem real_nonliteral :
    rootOut ∉ ordinary.equations ∧ childOut ∉ ordinary.equations ∧
    ∃ m, Models ordinary m ∧ Evidence registry interpretation m root dict :=
  ⟨literal_absent.1,literal_absent.2,assignment,populated,every_model _ populated⟩

end Yulang.GeneralDeclarativeNamedAliasResolve325
