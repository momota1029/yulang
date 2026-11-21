import Yulang.GeneralDeclarativeEntailment320
import Yulang.GeneralDeclarativeEvidence320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14500
set_option maxHeartbeats 4300000
namespace Yulang.GeneralDeclarativeCompilerTree320
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeAssembly320 (Node ChosenRecipe chosen_sound)
open GeneralDeclarativeEntailment320 (BatchRecipe batch_recipe_sound)
open GeneralDeclarativeEvidence320 (Local Evidence)
open GeneralDeclarations (Registry Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Dictionary Result Resolves Summarizes Classify All₂)

def LocalSound (r : Registry) (interp : Interpretation) (m : Assignment) (localRule : Local) : Prop :=
  ∀ d key kids, localRule d (.selected key kids) → Node r interp m d key kids

section
variable {r : Registry} {interp : Interpretation} {localRule : Local} {m : Assignment}

mutual
 theorem tree {d : Demand} (localSound : LocalSound r interp m localRule) (diagnostic : Tree)
    (dict : Dictionary) (resolves : Resolves localRule d diagnostic)
    (summary : Summarizes diagnostic (.selected dict)) : Evidence r interp m d dict := by
  cases resolves with
  | pending _ => cases summary
  | ambiguous _ => cases summary
  | rejected _ => cases summary
  | selected chosen children =>
    cases summary with
    | selected summarized combined =>
      cases combined with
      | selected exacts =>
        subst_vars
        exact .node (localSound _ _ _ chosen) (forest localSound _ _ children summarized)
 termination_by sizeOf diagnostic

 theorem forest {ds : List Demand} (localSound : LocalSound r interp m localRule)
    (diagnostics : List Tree) (dicts : List Dictionary)
    (resolves : All₂ (Resolves localRule) ds diagnostics)
    (summary : All₂ Summarizes diagnostics (dicts.map Result.selected)) :
    All₂ (Evidence r interp m) ds dicts := by
  cases dicts with
  | nil =>
    cases summary
    cases resolves
    exact .nil
  | cons dict tail =>
    cases summary with
    | cons first last =>
      cases resolves with
      | cons one rest =>
        exact .cons (tree localSound _ _ one first) (forest localSound _ _ rest last)
 termination_by sizeOf diagnostics
end

end

/-- Independent local classification must supply one ordinary recipe per
selected edge, which may be assembled by direct observations or by the
actual finite equation compiler. This is the remaining source theorem. -/
def Compiles (s : State) (r : Registry) (interp : Interpretation) (localRule : Local) : Prop :=
  ∀ d key kids, localRule d (.selected key kids) →
    ChosenRecipe s r interp d key kids ∨ BatchRecipe s r interp d key kids

theorem compile_classify {s r interp localRule d dict}
    (checked : Checked r) (producer : Compiles s r interp localRule)
    (m : Assignment) (valid : Models s m) (chosen : Classify localRule d (.selected dict)) :
    Evidence r interp m d dict := by
  obtain ⟨diagnostic,derivation,summary⟩ := chosen
  apply tree (m := m) (r := r) (interp := interp) (localRule := localRule) ?_ diagnostic dict derivation summary
  intro focus key kids picked
  rcases producer focus key kids picked with direct|compiled
  · exact chosen_sound checked direct m valid
  · exact batch_recipe_sound checked compiled m valid

end Yulang.GeneralDeclarativeCompilerTree320
