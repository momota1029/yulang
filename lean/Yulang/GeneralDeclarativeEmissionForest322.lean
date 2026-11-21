import Yulang.GeneralDeclarativeEmissionClause322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionForest322
open GeneralDeclarativeSourceEmission322 (Names demand)
open GeneralDeclarativeEmissionClause322 (Ready clause_ordinary)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeNodeFacts320 (clauseFacts)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeBatch320 (zipFacts)
open GeneralDeclarations (Declaration Clause)
open CommonRoleOutermostResolver (All₂)

structure Placement where
  compound : Clause → Nat → Capture
  targets : Clause → Nat → Nat

def children (decl : Declaration) (names : Names) (place : Placement) : List Demand :=
  decl.requirements.map fun c => demand decl c names (place.compound c) (place.targets c)

theorem all_clauses {s : State} {place : Placement}
    (coherent : Agree decl names)
    (ready : ∀ c ∈ decl.requirements, Ready s r interp decl c names (place.compound c) (place.targets c)) :
    Result s (zipFacts (clauseFacts r interp names.input) decl.requirements (children decl names place)) := by
  have aux (cs : List Clause) (valid : ∀ c ∈ cs, Ready s r interp decl c names (place.compound c) (place.targets c)) :
      All₂ (fun c d => Result s (clauseFacts r interp names.input c d))
        cs (cs.map fun c => demand decl c names (place.compound c) (place.targets c)) := by
    induction cs with
    | nil => exact .nil
    | cons first rest ih =>
      exact .cons (clause_ordinary coherent (valid first List.mem_cons_self))
        (ih (fun c h => valid c (List.mem_cons_of_mem _ h)))
  exact zip_result (aux decl.requirements ready)

end Yulang.GeneralDeclarativeEmissionForest322
