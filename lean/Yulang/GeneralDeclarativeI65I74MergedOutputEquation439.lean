import Yulang.GeneralDeclarativeI65I74MergedOutputEntry439
import Yulang.GeneralNominalDemandMerging

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalDemandMerging (Site SameInputs outputAtoms output_atoms_exact)
open GeneralSourceState (Output)
open Checker408 (Problem Result)

private theorem original_child_role_has_arity_zero439 {s q} (a : Original439 s q) :
    ((authoredRegistry s.core.current).roles a.childRole).arity = 0 := by
  have valid := a.checked.2 _ (List.mem_of_getElem? a.frame.authored)
  have signed := valid.signature.2.2.2 a.firstClause (by rw [a.originalClauses]; simp)
  have length := signed.1
  rw [a.firstArgs,a.firstRole] at length
  exact length.symm

private theorem original_merged_output_is_declared439 {s q} (a : Original439 s q) :
    ∃ body, ((authoredRegistry s.core.current).roles a.childRole).assoc a.outName = some body := by
  have valid := a.checked.2 _ (List.mem_of_getElem? a.frame.authored)
  have signed := valid.signature.2.2.2 a.firstClause (by rw [a.originalClauses]; simp)
  have declared := signed.2 a.firstEquation (by rw [a.firstOutput]; simp)
  simpa [GeneralDeclarations.Declared,a.firstRole,a.firstName] using declared

/-- Only a projection to the old demand-merge operation: the older
Site's ordinal is filled with the original clause ID for display.
It is not a comparison of physical allocation identity or a replay
of the old solver journal. The proof below uses role and outputs,
with no unnamed cells in either site. -/
def projectNullarySite439 {s q} (a : Original439 s q) (first : Bool) :
    Site (authoredRegistry s.core.current).roles := by
  let target := if first then a.leftCell else a.rightCell
  let cid := if first then a.firstClause.id else a.lastClause.id
  refine ⟨⟨cid,⟨a.childRole,fun _ => (0,0),[⟨a.outName,target⟩],?_⟩⟩,[],?_⟩
  · intro output seen
    obtain rfl := List.mem_singleton.mp seen
    exact original_merged_output_is_declared439 a
  · exact (original_child_role_has_arity_zero439 a).symm

theorem sites_project_exact_ordered_requests439 {s q} (a : Original439 s q) :
    ∃ left right : Request, frameWhereKids400 a.frame = [left,right] ∧
      left.occurrence = q.occurrence ++ [0] ∧ right.occurrence = q.occurrence ++ [1] ∧
      left.demand.role = (projectNullarySite439 a true).occurrence.demand.role ∧
      right.demand.role = (projectNullarySite439 a false).occurrence.demand.role ∧
      left.demand.outputs = (projectNullarySite439 a true).occurrence.demand.outputs ∧
      right.demand.outputs = (projectNullarySite439 a false).occurrence.demand.outputs ∧
      a.representative.demand.outputs = left.demand.outputs ++ right.demand.outputs :=
  ⟨_,_,a.exactKids,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem emitted_nullary_sites_have_same_inputs439 {s q} (a : Original439 s q)
    (models : GeneralNominalCommonBridge.Assignment → Prop) :
    SameInputs models (projectNullarySite439 a true) (projectNullarySite439 a false) :=
  ⟨rfl,.nil⟩

theorem emitted_merge_equations_are_exact439 {s q} (a : Original439 s q) :
    outputAtoms (projectNullarySite439 a true) (projectNullarySite439 a false) =
      GeneralNominalAllocation.equations a.leftCell (.var a.rightCell) := by
  simp [projectNullarySite439,outputAtoms]

theorem actual_output_merge_atoms_mean_same_named_equation439 {s q} (a : Original439 s q)
    (m : I72.Model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m.assignment
      (outputAtoms (projectNullarySite439 a true) (projectNullarySite439 a false)) ↔ a.MergedOutput m := by
  rw [emitted_merge_equations_are_exact439]
  exact GeneralNominalCaptureMerges.equations_exact _ _ _

theorem accepted_merged_report_rules_out_old_operation_atoms439 (p : Problem) (r : Result) (w : Wire439)
    (yes : check p r (.mergedOutput w) = true) :
    ∃ a : Original439 p.state p.root, r = a.report ∧
      ¬ ∃ m : I72.Model, I72.Fits p.state m ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model m.assignment
          (outputAtoms (projectNullarySite439 a true) (projectNullarySite439 a false)) := by
  obtain ⟨a,_,report⟩ := checked_merged_replay_matches_exact_tree439 yes
  exact ⟨a,report,fun ⟨m,fit,rows⟩ => no_fitting_extension_equalizes_the_named_output439 a
    ⟨m,fit,(actual_output_merge_atoms_mean_same_named_equation439 a m).mp rows⟩⟩

end Yulang.GeneralDeclarativeI65.I72.MergedOutput439
