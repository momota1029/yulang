import Yulang.GeneralDeclarativeNFClassify324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEvidenceFold325
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

def LocalWitness (r : Registry) (i : Interpretation) (s : State)
    (rules : Demand → Frontier Demand → Prop) : Prop :=
  ∀ m, Models s m → ∀ d, Declared r d → ∀ key kids, rules d (.selected key kids) →
    (∃ impl cap, impl.id = key ∧ Meaning r i m d impl cap kids) ∧
      ∀ child ∈ kids, Declared r child

section
variable {r : Registry} {i : Interpretation} {s : State}
  {rules : Demand → Frontier Demand → Prop} {m : Assignment}
mutual
theorem node (localRule : LocalWitness r i s rules) (valid : Models s m) (wanted : Declared r d)
    (diag : Tree) (dict : Dictionary) (steps : Resolves rules d diag)
    (returned : Summarizes diag (.selected dict)) : Evidence r i m d dict := by
  cases steps with
  | pending _ => cases returned
  | rejected _ => cases returned
  | ambiguous _ => cases returned
  | selected choice together =>
    have ⟨here, ready⟩ := localRule m valid _ wanted _ _ choice
    cases returned with
    | selected all merged =>
      cases merged with
      | selected childMatch =>
        subst_vars
        exact .node here (children localRule valid ready _ _ together all)
termination_by sizeOf diag

theorem children (localRule : LocalWitness r i s rules) (valid : Models s m)
    (wanted : ∀ d ∈ ds, Declared r d) (diags : List Tree) (dicts : List Dictionary)
    (steps : All₂ (Resolves rules) ds diags)
    (returned : All₂ Summarizes diags (dicts.map Result.selected)) : All₂ (Evidence r i m) ds dicts := by
  cases dicts with
  | nil => cases returned; cases steps; exact .nil
  | cons first rest =>
    cases returned with
    | cons won later =>
      cases steps with
      | cons firstRead afterRead =>
        exact .cons (node localRule valid (wanted _ List.mem_cons_self) _ _ firstRead won)
          (children localRule valid (fun d h => wanted d (List.mem_cons_of_mem _ h)) _ _ afterRead later)
termination_by sizeOf diags
end

theorem same_model (localRule : LocalWitness r i s rules) (valid : Models s m) (wanted : Declared r d)
    (chosen : Classify rules d (.selected dict)) : Evidence r i m d dict := by
  obtain ⟨diag,steps,returned⟩ := chosen
  exact node localRule valid wanted diag dict steps returned
end

end Yulang.GeneralDeclarativeEvidenceFold325
