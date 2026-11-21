import Yulang.GeneralDeclarativeRigidLocal323
import Yulang.GeneralDeclarativePriority321
import Yulang.GeneralDeclarativeEvidence320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeClosedTree323
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (BatchRecipe batch_recipe_sound)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeRigidLocal323 (RigidReads RootClosed exact_batch)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Dictionary Classify Resolves Summarizes All₂ Result Frontier)

/-- A witness at the actual source occurrence. Closure of requested results
is assessed against the entire ordinary state, not used to choose fields
or generate a different child. The conjunct is explicit in this proof
interface; no new local diagnostic is defined. -/
structure Frame (s : State) (r : Registry) (interp : Interpretation) (d : Demand)
    (key : Nat) (kids : List Demand) : Prop where
  source : ∃ impl names place,
    impl ∈ r.declarations ∧ impl.role = d.role ∧ impl.id = key ∧ children impl names place = kids ∧
    RigidReads s r interp d impl names place ∧ RootClosed s r interp d impl names.input

/-- Witnesses only at the visited successful nodes. A registry need not
promise closure of outputs for unselected or unsupported demands. -/
inductive Certified (s : State) (r : Registry) (interp : Interpretation) :
    Demand → Tree → Prop where
  | selected : Frame s r interp d key kids →
      All₂ (Certified s r interp) kids trees → Certified s r interp d (.selected key trees)

mutual
 theorem tree {s : State} {r : Registry} {interp : Interpretation}
    (checked : Checked r) (metaOK : Coverage r interp)
    (valid : Models s m) (asked : Declared r d)
    (treeSyntax : Tree) (dictionary : Dictionary)
    (proof : Certified s r interp d treeSyntax)
    (found : Summarizes treeSyntax (.selected dictionary)) :
    Evidence r interp m d dictionary := by
  cases proof with
  | selected frame kids =>
    obtain ⟨impl,names,place,visible,role,rfl,rfl,reads,closed⟩ := frame.source
    cases found with
    | selected summarized combined =>
      cases combined with
      | selected exactKeys =>
        subst_vars
        exact .node (batch_recipe_sound checked
          (exact_batch checked metaOK visible role asked reads closed) _ valid)
          (forest checked metaOK valid (fun child used => child_declared checked visible used) _ _ kids summarized)
 termination_by sizeOf treeSyntax

 theorem forest {s : State} {r : Registry} {interp : Interpretation}
    (checked : Checked r) (metaOK : Coverage r interp) (valid : Models s m)
    (asked : ∀ child ∈ ds, Declared r child) (diags : List Tree) (dicts : List Dictionary)
    (proof : All₂ (Certified s r interp) ds diags)
    (found : All₂ Summarizes diags (dicts.map Result.selected)) :
    All₂ (Evidence r interp m) ds dicts := by
  cases dicts with
  | nil =>
    cases found
    cases proof
    exact .nil
  | cons one rest =>
    cases found with
    | cons here later =>
      cases proof with
      | cons first tail =>
        exact .cons
          (tree checked metaOK valid (asked _ List.mem_cons_self) _ _ first here)
          (forest checked metaOK valid
            (fun child used => asked child (List.mem_cons_of_mem _ used)) _ _ tail later)
 termination_by sizeOf diags
end

end Yulang.GeneralDeclarativeClosedTree323
