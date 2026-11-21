import Yulang.GeneralDeclarativeNFComplete324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNFClassify324
open GeneralDeclarations (Checked Registry Declaration)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeModelStable324 (StableUnder)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeNFComplete324 (ReadBack local_sound facts produces)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEvidence320 (Evidence)

open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

def Observed (s : State) (r : Registry) (interp : Interpretation)
    (d : Demand) (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ names place, children impl names place = kids ∧
    ReadBack s r interp d impl names place ∧ BodyCoverage r interp d impl

abbrev Rule (s : State) (r : Registry) (interp : Interpretation)
    (support : Supported s completed) (tests : GeneralDeclarativePriority321.Candidates) :=
  Local s r interp support tests (Observed s r interp)

def SourceEnabled (s : State) (r : Registry) (interp : Interpretation)
    (rule : Demand → Frontier Demand → Prop) (eq : Equation) : Prop :=
  ∃ d impl names place, impl ∈ r.declarations ∧ impl.role = d.role ∧
    rule d (.selected impl.id (children impl names place)) ∧
    ReadBack s r interp d impl names place ∧ SourceEquation r interp d impl names.input eq

section
variable {s : State} {r : Registry} {interp : Interpretation}
    {complete : Nat → Prop} {support : Supported s complete}
    {tests : GeneralDeclarativePriority321.Candidates}

theorem local_compiler (checked : Checked r)
    (closed : StableUnder s (SourceEnabled s r interp (Rule s r interp support tests)))
    (asked : Declared r d)
    (selected : Rule s r interp support tests d (.selected key kids)) :
    ∃ impl names place, impl.id = key ∧ impl ∈ r.declarations ∧ children impl names place = kids ∧
      GeneralDeclarativeCompileLists321.Result s (facts r interp names.input impl d kids) := by
  obtain ⟨impl,rfl,⟨⟨visible,role⟩,_⟩,names,place,rfl,view,cover⟩ := selected_generated selected
  exact ⟨impl,names,place,rfl,visible,rfl,produces checked visible role asked cover view
    (fun e rule => closed e ⟨d,impl,names,place,visible,role,selected,view,rule⟩)⟩

mutual
 theorem tree (checked : Checked r)
    (closed : StableUnder s (SourceEnabled s r interp (Rule s r interp support tests)))
    (asked : Declared r d) (valid : Models s m) (diag : Tree) (dict : Dictionary)
    (ran : Resolves (Rule s r interp support tests) d diag) (done : Summarizes diag (.selected dict)) :
    Evidence r interp m d dict := by
  cases ran with
  | pending _ => cases done
  | ambiguous _ => cases done
  | rejected _ => cases done
  | selected own kids =>
    obtain ⟨impl,rfl,⟨⟨visible,role⟩,_⟩,names,place,rfl,view,cover⟩ := selected_generated own
    have closedHere : StableUnder s (SourceEquation r interp d impl names.input) :=
      fun e rule => closed e ⟨d,impl,names,place,visible,role,own,view,rule⟩
    cases done with
    | selected summaries combined =>
      cases combined with
      | selected linked =>
        subst_vars
        exact .node ⟨impl,names.input,rfl,local_sound checked visible role asked cover view closedHere m valid⟩
          (forest checked closed (fun _ seen => child_declared checked visible seen) valid _ _ kids summaries)
 termination_by sizeOf diag

 theorem forest (checked : Checked r)
    (closed : StableUnder s (SourceEnabled s r interp (Rule s r interp support tests)))
    (asked : ∀ d ∈ ds, Declared r d) (valid : Models s m) (diags : List Tree) (dicts : List Dictionary)
    (ran : All₂ (Resolves (Rule s r interp support tests)) ds diags)
    (done : All₂ Summarizes diags (dicts.map Result.selected)) : All₂ (Evidence r interp m) ds dicts := by
  cases dicts with
  | nil =>
    cases done
    cases ran
    exact .nil
  | cons first rest =>
    cases done with
    | cons won future =>
      cases ran with
      | cons firstRead restRead =>
        exact .cons (tree checked closed (asked _ List.mem_cons_self) valid _ _ firstRead won)
          (forest checked closed (fun child used => asked child (List.mem_cons_of_mem _ used)) valid _ _ restRead future)
 termination_by sizeOf diags
end

/-- This closes the recursive part for the fully normalized local
interface, including named where RHSs. No conclusion is made for a
source region that does not yet supply the independent observations. -/
theorem sound (checked : Checked r)
    (closed : StableUnder s (SourceEnabled s r interp (Rule s r interp support tests)))
    (asked : Declared r d) (valid : Models s m)
    (selected : Classify (Rule s r interp support tests) d (.selected dict)) :
    Evidence r interp m d dict := by
  obtain ⟨diag,ran,done⟩ := selected
  exact tree checked closed asked valid diag dict ran done

end

end Yulang.GeneralDeclarativeNFClassify324
