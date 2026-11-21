import Yulang.GeneralDeclarativeAssocRule323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAppliedTree323
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeRigidLocal323 (RigidReads)
open GeneralDeclarativeStableRigid323 (Rule)
open GeneralDeclarativeClosedTree323 (Certified)
open GeneralDeclarativeAssocRule323 (SourceEquation from_source_closure)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Tree Dictionary Classify Resolves Summarizes All₂ Result Frontier)

/-- The independently specified ordinary rule has fired for the actual
visible chosen declaration, at the actual capture and original demand.
Only equations from the parsed explicit/default RHS are considered. -/
def Applied (s : State) (r : Registry) (interp : Interpretation)
    (rule : Demand → Frontier Demand → Prop) : Prop :=
  ∀ d impl names place, impl ∈ r.declarations →
    rule d (.selected impl.id (children impl names place)) →
    RigidReads s r interp d impl names place →
    ∀ row, SourceEquation r interp d impl names.input row → row ∈ s.equations

section
variable {s : State} {r : Registry} {interp : Interpretation}
    {complete : Nat → Prop} {support : Supported s complete}
    {tests : GeneralDeclarativePriority321.Candidates}

mutual
 theorem certify (checked : Checked r) (metadata : Coverage r interp)
    (updates : Applied s r interp (Rule (r := r) (interp := interp) support tests))
    (tree : Tree) (dict : Dictionary)
    (resolved : Resolves (Rule (r := r) (interp := interp) support tests) d tree)
    (successful : Summarizes tree (.selected dict)) : Certified s r interp d tree := by
  cases resolved with
  | pending _ => cases successful
  | rejected _ => cases successful
  | ambiguous _ => cases successful
  | selected choice kids =>
    obtain ⟨impl,rfl,⟨⟨visible,role⟩,_⟩,names,place,rfl,seen⟩ := selected_generated choice
    have closed := from_source_closure checked metadata visible (updates d impl names place visible choice seen)
    cases successful with
    | selected agrees merged =>
      cases merged with
      | selected sameKeys =>
        subst_vars
        exact .selected ⟨impl,names,place,visible,role,rfl,rfl,seen,closed⟩
          (certify_children checked metadata updates _ _ kids agrees)
 termination_by sizeOf tree

 theorem certify_children (checked : Checked r) (metadata : Coverage r interp)
    (updates : Applied s r interp (Rule (r := r) (interp := interp) support tests))
    (trees : List Tree) (dicts : List Dictionary)
    (resolved : All₂ (Resolves (Rule (r := r) (interp := interp) support tests)) ds trees)
    (successful : All₂ Summarizes trees (dicts.map Result.selected)) :
    All₂ (Certified s r interp) ds trees := by
  cases dicts with
  | nil =>
    cases successful
    cases resolved
    exact .nil
  | cons first rest =>
    cases successful with
    | cons head tail =>
      cases resolved with
      | cons one many =>
        exact .cons (certify checked metadata updates _ _ one head)
          (certify_children checked metadata updates _ _ many tail)
 termination_by sizeOf trees
end

/-- Soundness for the independently presented rigid source fragment
once the actual parsed ordinary associated rules have been applied.
The evidence uses one identical arbitrary model at every node. -/
theorem rule_sound (checked : Checked r) (metadata : Coverage r interp)
    (updates : Applied s r interp (Rule (r := r) (interp := interp) support tests))
    (asked : Declared r d) (model : Models s m)
    (selected : Classify (Rule (r := r) (interp := interp) support tests) d (.selected dict)) :
    Evidence r interp m d dict := by
  obtain ⟨tree,resolved,summarized⟩ := selected
  exact GeneralDeclarativeClosedTree323.tree checked metadata model asked tree dict
    (certify checked metadata updates tree dict resolved summarized) summarized

end

end Yulang.GeneralDeclarativeAppliedTree323
