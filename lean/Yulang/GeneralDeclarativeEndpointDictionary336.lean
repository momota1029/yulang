import Yulang.GeneralDeclarativeEndpointSelected336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointDictionary336
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointOverlay336 (ModelsWith)
open GeneralDeclarativeEndpointSelected336 (Node Rule selected_sound selected_witness)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

def LocalNode (r : Registry) (i : Interpretation) (m : Assignment) (d : Demand)
    (key : Nat) (children : List Demand) : Prop :=
  ∃ impl cap spans, impl.id = key ∧ Node r i m d impl cap children spans

inductive Evidence (r : Registry) (i : Interpretation) (m : Assignment) : Demand → Dictionary → Prop where
  | node : LocalNode r i m d key kids →
      All₂ (Evidence r i m) kids entries →
      Evidence r i m d (.node key entries)

section
variable {r : Registry} {i : Interpretation} {s : State}
  {p : Supported s done} {m : Assignment}
  {waiting : Demand → Declaration → Prop}
mutual
theorem tree_sound (checked : Checked r) (covered : Coverage r i) (fit : ModelsWith s sidecar m)
    (d : Demand) (wanted : Declared r d) (diag : Tree) (dict : Dictionary)
    (steps : Resolves (Rule p sidecar r i waiting) d diag)
    (returned : Summarizes diag (.selected dict)) : Evidence r i m d dict := by
  cases steps with
  | pending _ => cases returned
  | rejected _ => cases returned
  | ambiguous _ => cases returned
  | selected candidate all =>
    obtain ⟨impl,key_is,⟨choice⟩⟩ := selected_witness candidate
    obtain ⟨⟨cap,actual⟩,children⟩ := selected_sound choice checked covered wanted m fit
    cases returned with
    | selected allReturned merged =>
      cases merged with
      | selected childMatch =>
        subst_vars
        exact .node ⟨impl,cap,choice.spans,rfl,actual⟩
          (forest_sound checked covered fit _ children _ _ all allReturned)
termination_by sizeOf diag

theorem forest_sound (checked : Checked r) (covered : Coverage r i) (fit : ModelsWith s sidecar m)
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
          (forest_sound checked covered fit _ (fun _ used => wanted _ (List.mem_cons_of_mem _ used))
            _ _ after last)
termination_by sizeOf diags
end

/-- Every node of the successful mixed declarative tree uses the
same *current* ordinary+projection model, not separate per-node
extensions. Exact chosen where order, fixed output targets and
post-selection sharing come from the unchanged compiler. -/
theorem dictionary_sound (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (accepted : Classify (Rule p sidecar r i waiting) d (.selected dict)) :
    ∀ m, ModelsWith s sidecar m → Evidence r i m d dict := by
  intro model fit
  obtain ⟨tree,seen,result⟩ := accepted
  exact tree_sound checked covered fit d wanted tree dict seen result
end

end Yulang.GeneralDeclarativeEndpointDictionary336
