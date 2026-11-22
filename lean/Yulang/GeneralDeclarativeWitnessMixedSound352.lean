import Yulang.GeneralDeclarativeWitnessMixedForest352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedSound352
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessMixedForest352 (Problem Global Rule local_sound)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarations (Checked)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Result Tree Dictionary Classify Resolves Summarizes All₂)

section
variable {p : Problem} {g : Global p} {m : Assignment}
local notation "R" => registry g.table
local notation "I" => interpretation g.table.snapshot

mutual
theorem tree (checked : Checked R) (covered : Coverage R I) (fit : ModelsExact p.current sidecar m)
    (d : Demand) (wanted : Declared R d) (diag : Tree) (dict : Dictionary)
    (steps : Resolves (Rule g sidecar) d diag)
    (returned : Summarizes diag (.selected dict)) : Evidence R I m d dict := by
  cases steps with
  | pending _ => cases returned
  | rejected _ => cases returned
  | ambiguous _ => cases returned
  | selected candidate all =>
    obtain ⟨node,children⟩ := local_sound candidate checked covered wanted m fit
    cases returned with
    | selected allReturned merged =>
      cases merged with
      | selected childMatch =>
        subst_vars
        exact .node node (forest checked covered fit _ children _ _ all allReturned)
termination_by sizeOf diag

theorem forest (checked : Checked R) (covered : Coverage R I) (fit : ModelsExact p.current sidecar m)
    (ds : List Demand) (wanted : ∀ child ∈ ds, Declared R child) (diags : List Tree) (dicts : List Dictionary)
    (steps : All₂ (Resolves (Rule g sidecar)) ds diags)
    (returned : All₂ Summarizes diags (dicts.map Result.selected)) : All₂ (Evidence R I m) ds dicts := by
  cases dicts with
  | nil => cases returned; cases steps; exact .nil
  | cons one rest =>
    cases returned with
    | cons first last =>
      cases steps with
      | cons item after =>
        exact .cons (tree checked covered fit _ (wanted _ List.mem_cons_self) _ _ item first)
          (forest checked covered fit _ (fun _ used => wanted _ (List.mem_cons_of_mem _ used)) _ _ after last)
termination_by sizeOf diags
end

/-- The same assignment interprets all checked record projections,
tagged captures, child demands and associated outputs. -/
theorem dictionary_sound (checked : Checked R) (covered : Coverage R I) (wanted : Declared R d)
    (selected : Classify (Rule g sidecar) d (.selected dict))
    (fit : ModelsExact p.current sidecar m) : Evidence R I m d dict := by
  obtain ⟨diag,steps,shown⟩ := selected
  exact tree checked covered fit d wanted diag dict steps shown

end
end Yulang.GeneralDeclarativeWitnessMixedSound352
