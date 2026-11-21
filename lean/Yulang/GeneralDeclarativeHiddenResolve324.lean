import Yulang.GeneralDeclarativeHiddenReads324
import Yulang.GeneralDeclarativeCompilerTree320
import Yulang.GeneralDeclarativeNamedTree320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenResolve324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenProbe324 (traces leaf_traces ready_root ready_child tests safe)
open GeneralDeclarativeHiddenReads324
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeNFResolve324 (Rule)
open GeneralDeclarativeNFNode324 (meaning)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeAssembly320 (ChosenRecipe Meaning)
open GeneralDeclarativeEntailment320 (BatchRecipe Holds)
open GeneralDeclarativeCompilerTree320 (Compiles)
open GeneralDeclarativeNamedTree320 (position)
open GeneralDeclarativeNodeFacts320 (nodeFacts)
open GeneralDeclarativeBatch320 (zipFacts)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify Dictionary All₂)

theorem root_only (decl) (present : decl ∈ registry.declarations) (role : decl.role = root.role) :
    decl = parent := by
  rcases List.mem_cons.mp present with same|later
  · exact same
  · cases List.mem_singleton.mp later
    cases role

theorem child_only (decl) (present : decl ∈ registry.declarations) (role : decl.role = child.role) :
    decl = leaf := by
  rcases List.mem_cons.mp present with same|later
  · cases same
    cases role
  · exact List.mem_singleton.mp later

abbrev branch (completed : Nat → Prop) := Rule final registry interpretation (support completed) (tests completed)

theorem root_chosen (completed : Nat → Prop) : branch completed root (.selected parent.id [child]) := by
  refine .selected (ready_root completed) (safe completed _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,traces completed⟩ ?_ root_generated
  · rintro ⟨decl,⟨listed,role⟩,unknown⟩
    cases root_only decl listed role
    exact unknown (traces completed)
  · rintro decl ⟨⟨visible,role⟩,_⟩
    rw [root_only decl visible role]

theorem child_chosen (completed : Nat → Prop) : branch completed child (.selected leaf.id []) := by
  refine .selected (ready_child completed) (safe completed _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,leaf_traces completed⟩ ?_ child_generated
  · rintro ⟨decl,⟨listed,role⟩,unknown⟩
    cases child_only decl listed role
    exact unknown (leaf_traces completed)
  · rintro decl ⟨⟨visible,role⟩,_⟩
    rw [child_only decl visible role]

abbrev dictionary : Dictionary := .node parent.id [.node leaf.id []]

theorem final_selected (completed : Nat → Prop) : Classify (branch completed) root (.selected dictionary) :=
  ⟨.selected parent.id [.selected leaf.id []],
    .selected (root_chosen completed) (.cons (.selected (child_chosen completed) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem root_meaning (m : Assignment) (v : Models final m) : Meaning registry interpretation m root parent names.input [child] := by
  rw [← exact_child]
  exact meaning checked List.mem_cons_self rfl declared_root body_root root_reads stable_root m v

theorem child_meaning (m : Assignment) (v : Models final m) :
    Meaning registry interpretation m child leaf leafNames.input [] :=
  meaning checked (List.mem_cons_of_mem _ List.mem_cons_self) rfl declared_child body_child leaf_reads stable_child m v

theorem final_evidence (m : Assignment) (v : Models final m) : Evidence registry interpretation m root dictionary :=
  .node ⟨parent,names.input,rfl,root_meaning m v⟩
    (.cons (.node ⟨leaf,leafNames.input,rfl,child_meaning m v⟩ .nil) .nil)

theorem final_inhabited :
    Classify (branch (fun _ => True)) root (.selected dictionary) ∧
    Models final (assignment true) ∧ Evidence registry interpretation (assignment true) root dictionary :=
  ⟨final_selected _,fits_final,final_evidence _ fits_final⟩

/-- The old producer requires raw translation even for the erased branch.
This is a limitation of that producer, not a type inference rejection. -/
theorem no_raw_recipe : ¬ChosenRecipe final registry interpretation root parent.id [child] := by
  rintro ⟨decl,cap,_,typed⟩
  cases root_only decl typed.visible typed.role
  have atRoot := position typed.head (show root.arguments[0]? = some (GeneralDeclarativeExampleSource320.point 0) from rfl)
    (show parent.head[0]? = some raw from rfl)
  obtain ⟨_,_,compiled,_⟩ := atRoot
  rw [raw_does_not_compile] at compiled
  cases compiled

theorem no_raw_batch : ¬BatchRecipe final registry interpretation root parent.id [child] := by
  rintro ⟨decl,cap,_,same,vis,_,_,built,_⟩
  have pick : decl = parent := by
    rcases List.mem_cons.mp vis with h|h
    · exact h
    · cases List.mem_singleton.mp h
      cases same
  subst decl
  change (if parent.role = root.role then do
    let h ← zipFacts (GeneralDeclarativeArgumentFacts320.headFact catalogue interpretation cap) root.arguments parent.head
    let k ← zipFacts (GeneralDeclarativeNodeFacts320.clauseFacts registry interpretation cap) parent.requirements [child]
    let o ← GeneralDeclarativeBatch320.collect (GeneralDeclarativeOutputFacts320.rootFact registry interpretation parent root cap) root.outputs
    pure (h ++ k ++ o)
    else none) = some _ at built
  have h : zipFacts (GeneralDeclarativeArgumentFacts320.headFact catalogue interpretation cap) root.arguments parent.head = none := rfl
  simp [h] at built

theorem old_producer_fails (completed : Nat → Prop) : ¬Compiles final registry interpretation (branch completed) := by
  intro all
  rcases all root parent.id [child] (root_chosen completed) with left|right
  · exact no_raw_recipe left
  · exact no_raw_batch right

end Yulang.GeneralDeclarativeHiddenResolve324
