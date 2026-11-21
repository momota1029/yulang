import Yulang.GeneralDeclarativeNFNode324
import Yulang.GeneralDeclarativeOutputRequests323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNFResolve324
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeNFNode324 (Reads BodyCoverage meaning)
open GeneralDeclarativeModelStable324 (StableUnder)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

def Generates (s : State) (r : Registry) (interp : Interpretation) (d : Demand)
    (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ names place, children impl names place = kids ∧
    Reads s r interp d impl names place ∧ BodyCoverage r interp d impl

abbrev Rule (s : State) (r : Registry) (interp : Interpretation)
    (support : Supported s completed) (tests : GeneralDeclarativePriority321.Candidates) :=
  Local s r interp support tests (Generates s r interp)

def Enabled (s : State) (r : Registry) (interp : Interpretation)
    (rule : Demand → Frontier Demand → Prop) (row : Equation) : Prop :=
  ∃ d impl names place, impl ∈ r.declarations ∧ impl.role = d.role ∧
    rule d (.selected impl.id (children impl names place)) ∧
    Reads s r interp d impl names place ∧ SourceEquation r interp d impl names.input row

section
variable {s : State} {r : Registry} {interp : Interpretation}
    {complete : Nat → Prop} {support : Supported s complete}
    {tests : GeneralDeclarativePriority321.Candidates}

mutual
 theorem tree (checked : Checked r)
    (closed : StableUnder s (Enabled s r interp (Rule s r interp support tests)))
    (requested : Declared r d) (valid : Models s m) (diagnostic : Tree) (dict : Dictionary)
    (ran : Resolves (Rule s r interp support tests) d diagnostic)
    (done : Summarizes diagnostic (.selected dict)) : Evidence r interp m d dict := by
  cases ran with
  | pending _ => cases done
  | rejected _ => cases done
  | ambiguous _ => cases done
  | selected selected kids =>
    obtain ⟨impl,rfl,⟨⟨vis,role⟩,_⟩,names,place,rfl,reads,covers⟩ := selected_generated selected
    have stableRule : StableUnder s (SourceEquation r interp d impl names.input) :=
      fun row law => closed row ⟨d,impl,names,place,vis,role,selected,reads,law⟩
    cases done with
    | selected summaries merged =>
      cases merged with
      | selected keys =>
        subst_vars
        exact .node ⟨impl,names.input,rfl,meaning checked vis role requested covers reads stableRule m valid⟩
          (forest checked closed (fun child present => child_declared checked vis present) valid _ _ kids summaries)
 termination_by sizeOf diagnostic

 theorem forest (checked : Checked r)
    (closed : StableUnder s (Enabled s r interp (Rule s r interp support tests)))
    (requested : ∀ d ∈ ds, Declared r d) (valid : Models s m) (trees : List Tree) (dicts : List Dictionary)
    (ran : All₂ (Resolves (Rule s r interp support tests)) ds trees)
    (done : All₂ Summarizes trees (dicts.map Result.selected)) :
    All₂ (Evidence r interp m) ds dicts := by
  cases dicts with
  | nil =>
    cases done
    cases ran
    exact .nil
  | cons first rest =>
    cases done with
    | cons firstDone later =>
      cases ran with
      | cons firstRead afterRead =>
        exact .cons (tree checked closed (requested _ List.mem_cons_self) valid _ _ firstRead firstDone)
          (forest checked closed (fun d mem => requested d (List.mem_cons_of_mem _ mem)) valid _ _ afterRead later)
 termination_by sizeOf trees
end

theorem sound (checked : Checked r)
    (closed : StableUnder s (Enabled s r interp (Rule s r interp support tests)))
    (requested : Declared r d) (valid : Models s m)
    (result : Classify (Rule s r interp support tests) d (.selected dict)) :
    Evidence r interp m d dict := by
  obtain ⟨diagnostic,ran,done⟩ := result
  exact tree checked closed requested valid diagnostic dict ran done

end

end Yulang.GeneralDeclarativeNFResolve324
