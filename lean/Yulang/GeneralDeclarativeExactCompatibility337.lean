import Yulang.GeneralDeclarativeEndpointCompatibility336
import Yulang.GeneralDeclarativeExactDictionary337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactCompatibility337
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeWitnessHead334 (Actuals)
open GeneralDeclarativeWitnessNode334 (Witness)
open GeneralDeclarativeWitnessClassify334 (selected_witness)
open GeneralDeclarativeEndpointInput336 (Inputs)
open GeneralDeclarativeEndpointSelected336 (Selected)
open GeneralDeclarativeEndpointCompatibility336 (lift_witness)
open GeneralDeclarativeExactDictionary337 (Rule Evidence dictionary_sound)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open CommonRoleOutermostResolver (Tree Dictionary Classify Resolves Summarizes All₂ Result)

theorem local_positive {s : State} {p : Supported s done}
    (old : GeneralDeclarativeWitnessClassify334.Rule p r i wait d (.selected key kids)) :
    Rule p additional r i wait d (.selected key kids) := by
  obtain ⟨decl,id,⟨w⟩⟩ := selected_witness old
  rw [← id]
  exact .selected (lift_witness w)

section
variable {s : State} {p : Supported s done} {i : Interpretation} {r : Registry}
  {wait : Demand → Declaration → Prop}
mutual
theorem selected_tree (diag : Tree) (dict : Dictionary)
    (old : Resolves (GeneralDeclarativeWitnessClassify334.Rule p r i wait) d diag)
    (success : Summarizes diag (.selected dict)) :
    Resolves (Rule p additional r i wait) d diag := by
  cases old with
  | pending _ => cases success
  | rejected _ => cases success
  | ambiguous _ => cases success
  | selected root children =>
    cases success with
    | selected childrenOK joins =>
      cases joins with
      | selected eq =>
        subst_vars
        exact .selected (local_positive root) (selected_forest _ _ children childrenOK)
termination_by sizeOf diag

theorem selected_forest (diags : List Tree) (dicts : List Dictionary)
    (old : All₂ (Resolves (GeneralDeclarativeWitnessClassify334.Rule p r i wait)) ds diags)
    (success : All₂ Summarizes diags (dicts.map Result.selected)) :
    All₂ (Resolves (Rule p additional r i wait)) ds diags := by
  cases dicts with
  | nil => cases success; cases old; exact .nil
  | cons first rest =>
    cases success with
    | cons h t =>
      cases old with
      | cons one more => exact .cons (selected_tree _ _ one h) (selected_forest _ _ more t)
termination_by sizeOf diags
end

/-- Prior successful I-60 trees embed literally into exact residual semantics.
They do not require or reinterpret an old masked receipt. Nothing is claimed
about prior pending diagnoses or arbitrary raw legacy correspondences. -/
theorem old_success (old : Classify (GeneralDeclarativeWitnessClassify334.Rule p r i wait) d (.selected dict)) :
    Classify (Rule p additional r i wait) d (.selected dict) := by
  obtain ⟨diag,left,right⟩ := old
  exact ⟨diag,selected_tree diag dict left right,right⟩

theorem old_and_new (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (old : Classify (GeneralDeclarativeWitnessClassify334.Rule p r i wait) d (.selected dict))
    (m) (fit : Models s m) :
    GeneralDeclarativeEvidence320.Evidence r i m d dict ∧ Evidence r i m d dict := by
  exact ⟨GeneralDeclarativeWitnessClassify334.dictionary_sound checked covered wanted old m fit,
    dictionary_sound checked covered wanted (old_success (additional := []) old) m
      ⟨fit,fun _ h => False.elim (List.not_mem_nil h)⟩⟩
end

end Yulang.GeneralDeclarativeExactCompatibility337
