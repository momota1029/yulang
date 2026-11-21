import Yulang.GeneralDeclarativeAssembly320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeEvidence320
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeAssembly320 (ChosenRecipe Node chosen_sound)
open GeneralDeclarations (Registry Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Result Resolves Summarizes Classify All₂)

abbrev Local := Demand → Frontier Demand → Prop

/-- The single remaining local producer: the actual declarative selected
frontier must produce the checked ordinary read recipe. Neither executor nor
a choice among models can supply this premise. -/
def Produces (s : State) (r : Registry) (interp : Interpretation) (localRule : Local) : Prop :=
  ∀ d key children, localRule d (.selected key children) → ChosenRecipe s r interp d key children

inductive Evidence (r : Registry) (interp : Interpretation) (m : Assignment) : Demand → Dictionary → Prop where
  | node : Node r interp m d key children →
      All₂ (Evidence r interp m) children dictionaries →
      Evidence r interp m d (.node key dictionaries)

section
variable {s : State} {r : Registry} {interp : Interpretation} {localRule : Local}

mutual
 theorem tree_sound (checked : Checked r) (producer : Produces s r interp localRule)
    (m : Assignment) (valid : Models s m) (d : Demand) (tree : Tree) (dict : Dictionary)
    (complete : Resolves localRule d tree) (success : Summarizes tree (.selected dict)) :
    Evidence r interp m d dict := by
  cases complete with
  | pending _ => cases success
  | ambiguous _ => cases success
  | rejected _ => cases success
  | selected picked children =>
    cases success with
    | selected summarized combined =>
      cases combined with
      | selected eq =>
        subst_vars
        exact .node (chosen_sound checked (producer _ _ _ picked) m valid)
          (forest_sound checked producer m valid _ _ _ children summarized)
 termination_by sizeOf tree

 theorem forest_sound (checked : Checked r) (producer : Produces s r interp localRule)
    (m : Assignment) (valid : Models s m) (ds : List Demand) (trees : List Tree) (dicts : List Dictionary)
    (complete : All₂ (Resolves localRule) ds trees)
    (success : All₂ Summarizes trees (dicts.map Result.selected)) :
    All₂ (Evidence r interp m) ds dicts := by
  cases dicts with
  | nil =>
    cases success
    cases complete
    exact .nil
  | cons dict rest =>
    cases success with
    | cons first last =>
      cases complete with
      | cons resolved remaining =>
        exact .cons (tree_sound checked producer m valid _ _ _ resolved first)
          (forest_sound checked producer m valid _ _ rest remaining last)
 termination_by sizeOf trees
end

/-- Only a fully successful independent diagnostic tree is usable as a
dictionary. Both parent and every ordered child use the very same model
of the same declarative constraint state. No execution assumptions. -/
theorem classify_sound (checked : Checked r) (producer : Produces s r interp localRule)
    (m : Assignment) (valid : Models s m) {d : Demand} {dict : Dictionary}
    (accepted : Classify localRule d (.selected dict)) : Evidence r interp m d dict := by
  obtain ⟨tree,derived,complete⟩ := accepted
  exact tree_sound checked producer m valid d tree dict derived complete

end

end Yulang.GeneralDeclarativeEvidence320
