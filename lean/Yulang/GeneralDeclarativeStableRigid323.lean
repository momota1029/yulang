import Yulang.GeneralDeclarativeClosedTree323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableRigid323
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeRigidLocal323 (RigidReads RootClosed exact_batch)
open GeneralDeclarativeEntailment320 (Entails literal)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeClosedTree323 (Certified)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Dictionary Classify Resolves Summarizes All₂ Result Frontier)

/-- Positive independent source realization, without checking whether a
selected impl's associated rows have already entered the ordinary state. -/
def Generates (s : State) (r : Registry) (interp : Interpretation)
    (d : Demand) (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ names place, children impl names place = kids ∧ RigidReads s r interp d impl names place

/-- An ordinary fixed-state property of selected presentations in this
fragment. Only the precise root output rows are required, not any
recursive evidence or statement about stopped executions. -/
def Closed (s : State) (r : Registry) (interp : Interpretation)
    (rule : Demand → Frontier Demand → Prop) : Prop :=
  ∀ d impl names place,
    rule d (.selected impl.id (children impl names place)) →
    RigidReads s r interp d impl names place →
    RootClosed s r interp d impl names.input

theorem literal_closure {s : State} (h :
    ∀ d impl names place, rule d (.selected impl.id (children impl names place)) →
      RigidReads s r interp d impl names place →
      ∀ out ∈ d.outputs, ∀ row, rootFact r interp impl d names.input out = some [row] →
        row ∈ s.equations) :
    Closed s r interp rule :=
  fun d impl names place selected seen out there row exactOut =>
    literal (h d impl names place selected seen out there row exactOut)

section
variable {s : State} {r : Registry} {interp : Interpretation}
    {complete : Nat → Prop} {support : Supported s complete}
    {tests : GeneralDeclarativePriority321.Candidates}

abbrev Rule (support : Supported s complete) (tests : GeneralDeclarativePriority321.Candidates) :=
  Local s r interp support tests (Generates s r interp)

mutual
 theorem certify (settled : Closed s r interp (Rule (r := r) (interp := interp) support tests))
    (tree : Tree) (dict : Dictionary)
    (resolved : Resolves (Rule (r := r) (interp := interp) support tests) d tree)
    (successful : Summarizes tree (.selected dict)) : Certified s r interp d tree := by
  cases resolved with
  | pending _ => cases successful
  | rejected _ => cases successful
  | ambiguous _ => cases successful
  | selected choice kids =>
    obtain ⟨impl,rfl,visibleAndRole,names,place,rfl,seen⟩ := selected_generated choice
    have closed := settled d impl names place choice seen
    cases successful with
    | selected agrees merged =>
      cases merged with
      | selected sameKeys =>
        subst_vars
        exact .selected ⟨impl,names,place,visibleAndRole.1.1,visibleAndRole.1.2,rfl,rfl,seen,closed⟩
          (certify_children settled _ _ kids agrees)
 termination_by sizeOf tree

 theorem certify_children
    (settled : Closed s r interp (Rule (r := r) (interp := interp) support tests))
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
        exact .cons (certify settled _ _ one head)
          (certify_children settled _ _ many tail)
 termination_by sizeOf trees
end

theorem stable_sound (checked : Checked r) (metaOK : Coverage r interp)
    (settled : Closed s r interp (Rule (r := r) (interp := interp) support tests))
    (asked : Declared r d) (model : Models s m)
    (selected : Classify (Rule (r := r) (interp := interp) support tests) d (.selected dict)) :
    Evidence r interp m d dict := by
  obtain ⟨tree,resolved,summarized⟩ := selected
  exact GeneralDeclarativeClosedTree323.tree checked metaOK model asked tree dict
    (certify settled tree dict resolved summarized) summarized

end

end Yulang.GeneralDeclarativeStableRigid323
