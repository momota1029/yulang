import Yulang.GeneralDeclarativeTaggedSelected340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedDictionary340
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeTaggedSelected340 (Selected local_sound)
open GeneralDeclarativeExactDictionary337 (Evidence LocalNode)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

/-- Only a positive fragment of declarative classification. Old negative
diagnostics are not transported through a broader candidate observer.
Every selected node, including an old input route, uses the same
joined-aware unique-candidate test. -/
inductive Rule {s : State} (p : Supported s done) (sidecar : List GeneralDeclarativeEndpointOverlay336.Entry)
    (r : Registry) (i : Interpretation) (waiting : Demand → Declaration → Prop) : Demand → Frontier Demand → Prop where
  | whole : Selected p sidecar r i waiting d impl kids → Rule p sidecar r i waiting d (.selected impl.id kids)

theorem local_witness {s : State} {p : Supported s done}
    (known : Rule p sidecar r i waiting d (.selected key kids))
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (fit : ModelsExact s sidecar m) :
    LocalNode r i m d key kids ∧ ∀ child ∈ kids, Declared r child := by
  cases known with
  | whole new =>
    obtain ⟨⟨cap,actual⟩,children⟩ := local_sound new checked covered wanted m fit
    exact ⟨⟨_,cap,new.spans,rfl,actual⟩,children⟩

section
variable {r : Registry} {i : Interpretation} {s : State} {p : Supported s done}
  {waiting : Demand → Declaration → Prop}
mutual
theorem tree_sound (checked : Checked r) (covered : Coverage r i) (fit : ModelsExact s sidecar m)
    (d : Demand) (wanted : Declared r d) (diag : Tree) (dict : Dictionary)
    (steps : Resolves (Rule p sidecar r i waiting) d diag)
    (returned : Summarizes diag (.selected dict)) : Evidence r i m d dict := by
  cases steps with
  | pending _ => cases returned
  | rejected _ => cases returned
  | ambiguous _ => cases returned
  | selected candidate all =>
    obtain ⟨node,children⟩ := local_witness candidate checked covered wanted fit
    cases returned with
    | selected allReturned merged =>
      cases merged with
      | selected childMatch =>
        subst_vars
        exact .node node (forest_sound checked covered fit _ children _ _ all allReturned)
termination_by sizeOf diag

theorem forest_sound (checked : Checked r) (covered : Coverage r i) (fit : ModelsExact s sidecar m)
    (ds : List Demand) (wanted : ∀ child ∈ ds, Declared r child) (diags : List Tree) (dicts : List Dictionary)
    (steps : All₂ (Resolves (Rule p sidecar r i waiting)) ds diags)
    (returned : All₂ Summarizes diags (dicts.map Result.selected)) : All₂ (Evidence r i m) ds dicts := by
  cases dicts with
  | nil => cases returned; cases steps; exact .nil
  | cons one rest =>
    cases returned with
    | cons first last =>
      cases steps with
      | cons item after =>
        exact .cons (tree_sound checked covered fit _ (wanted _ List.mem_cons_self) _ _ item first)
          (forest_sound checked covered fit _ (fun _ used => wanted _ (List.mem_cons_of_mem _ used)) _ _ after last)
termination_by sizeOf diags
end

theorem dictionary_sound (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (selected : Classify (Rule p sidecar r i waiting) d (.selected dict))
    (fit : ModelsExact s sidecar m) : Evidence r i m d dict := by
  obtain ⟨tree,ran,shows⟩ := selected
  exact tree_sound checked covered fit d wanted tree dict ran shows
end

end Yulang.GeneralDeclarativeTaggedDictionary340
