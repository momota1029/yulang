import Yulang.GeneralDeclarativeCompoundDictionary338
import Yulang.GeneralDeclarativeMixedCompiler339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMixedDictionary339
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeMixedCompiler339 (Selected Node selected_sound)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

abbrev Former := @GeneralDeclarativeCompoundDictionary338.Rule

/-- Use the very same approved election in either route. Extending
the positive receipt witness does not add a selection priority or a
rejection rule; actual contradictions still use earlier I-58. -/
inductive Rule {s : State} (p : Supported s done) (reads : List Entry) (r : Registry)
    (i : Interpretation) (waiting : Demand → Declaration → Prop) : Demand → Frontier Demand → Prop where
  | previous : Former p reads r i waiting d verdict → Rule p reads r i waiting d verdict
  | compound : Selected p reads r i waiting d impl kids → Rule p reads r i waiting d (.selected impl.id kids)

def Meaning (r : Registry) (i : Interpretation) (m : Assignment) (d : Demand) (key : Nat)
    (kids : List Demand) : Prop :=
  GeneralDeclarativeCompoundDictionary338.Meaning r i m d key kids ∨
    ∃ impl cap spans, impl.id = key ∧ Node r i m d impl cap kids spans

theorem local_meaning {s : State} {p : Supported s done}
    (candidate : Rule p reads r i waiting d (.selected key kids))
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d) (fit : ModelsExact s reads m) :
    Meaning r i m d key kids ∧ ∀ child ∈ kids, Declared r child := by
  cases candidate with
  | previous old =>
    obtain ⟨prior,children⟩ := GeneralDeclarativeCompoundDictionary338.local_meaning old checked covered wanted fit
    exact ⟨.inl prior,children⟩
  | compound selected =>
    obtain ⟨⟨cap,body⟩,children⟩ := selected_sound selected checked covered wanted m fit
    exact ⟨.inr ⟨_,cap,selected.spans,rfl,body⟩,children⟩

inductive Evidence (r : Registry) (i : Interpretation) (m : Assignment) : Demand → Dictionary → Prop where
  | node : Meaning r i m d key kids → All₂ (Evidence r i m) kids entries →
      Evidence r i m d (.node key entries)

section
variable {r : Registry} {i : Interpretation} {s : State} {p : Supported s done} {m : Assignment}
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
    obtain ⟨actual,children⟩ := local_meaning candidate checked covered wanted fit
    cases returned with
    | selected allReturned merged =>
      cases merged with
      | selected childMatch =>
        subst_vars
        exact .node actual
          (forest_sound checked covered fit _ children _ _ all allReturned)
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
          (forest_sound checked covered fit _ (fun _ used => wanted _ (List.mem_cons_of_mem _ used))
            _ _ after last)
termination_by sizeOf diags
end

theorem dictionary_sound (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (accepted : Classify (Rule p sidecar r i waiting) d (.selected dict)) :
    ∀ m, ModelsExact s sidecar m → Evidence r i m d dict := by
  intro model fit
  obtain ⟨tree,seen,result⟩ := accepted
  exact tree_sound checked covered fit d wanted tree dict seen result
end

end Yulang.GeneralDeclarativeMixedDictionary339
