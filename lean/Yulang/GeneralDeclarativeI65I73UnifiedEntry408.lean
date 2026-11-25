import Yulang.GeneralDeclarativeI65I73UnifiedLedger408

namespace Yulang.GeneralDeclarativeI65.I72.Checker408
open GeneralSourceMetadataFiniteLookup291 (get)
open GeneralSourceMetadataRoles291 (index RoleRow indexed)

abbrev Problem := Check408.Problem
abbrev Result := Check408.Result
abbrev Witness := Check408.Witness
abbrev ClassifiedAs := Check408.ClassifiedAs
abbrev ReportEvidence := Check408.ReportEvidence

/-- A fallback arity does not declare a role. The positive branch
must find the actual authored role row of the original demand. -/
def originalRole (p : Problem) : Option RoleRow :=
  get p.root.demand.role (index p.state.core.current.environment.source.roles)

/-- The public uniform entry. The shared C408 branch engine is reused;
the nullary branch additionally checks the finite authored role table.
Raw-root K2 remains independent of source or pending-output metadata. -/
def check (p : Problem) (r : Result) (w : Witness) : Bool :=
  match w with
  | .rawRoot _ => Check408.check p r w
  | .nullary => (originalRole p).isSome && Check408.check p r w
  | .unsupported => false

theorem accepted_implies_branch_engine408 (p : Problem) (r : Result) (w : Witness)
    (accepted : check p r w = true) : Check408.check p r w = true := by
  cases w with
  | rawRoot => exact accepted
  | nullary => exact (GeneralDeclarativeWitnessProblem349.splitAnd accepted).2
  | unsupported => simp [check] at accepted

theorem nullary_checks_actual_declared_role408 (p : Problem) (r : Result)
    (accepted : check p r .nullary = true) :
    ∃ row : RoleRow, originalRole p = some row ∧
      row ∈ p.state.core.current.environment.source.roles.rows ∧ row.role = p.root.demand.role := by
  have present := (GeneralDeclarativeWitnessProblem349.splitAnd accepted).1
  cases actual : originalRole p with
  | none => simp [actual] at present
  | some row =>
    exact ⟨row,rfl,(indexed actual).1,(indexed actual).2⟩

theorem unseen_role_fallback_is_not_a_checked_nullary408 (p : Problem) (r : Result)
    (missing : originalRole p = none) : check p r .nullary = false := by
  simp [check,missing]

theorem selected_nullary_matches_only_row_of_that_role408 (p : Problem) (r : Result)
    (accepted : check p r .nullary = true) :
    ∃ (role : RoleRow) (d : GeneralDeclarations.Declaration),
      originalRole p = some role ∧ GeneralDeclarativeI65.visible p.state.core p.root = [d] ∧
      d.role = role.role ∧ r = Check408.nullaryReport d := by
  obtain ⟨role,read,_,roleName⟩ := nullary_checks_actual_declared_role408 p r accepted
  obtain ⟨d,rows,_,same⟩ := (Check408.bool_nullary_protocol_exact408 p r).mp
    (accepted_implies_branch_engine408 p r .nullary accepted)
  have visibleAt : d ∈ GeneralDeclarativeI65.visible p.state.core p.root := by simp [rows]
  have named := (GeneralDeclarativeI65.visible_exact p.state.core p.root d).mp visibleAt |>.2
  exact ⟨role,d,read,rows,named.trans roleName.symm,same⟩


/-- Uniform soundness of the actual public entry, with the original
R0 classification and the exact recorded report in every fitting
model of that same Problem. -/
theorem check_sound (p : Problem) (r : Result) (w : Witness)
    (accepted : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
      ∀ (m : I72.Model), Fits p.state m → ReportEvidence p.state m p.root r :=
  Check408.check_sound p r w (accepted_implies_branch_engine408 p r w accepted)

theorem checked_report_is_unique408 (p : Problem) (r a : Result) (x y : Witness)
    (first : check p r x = true) (second : check p a y = true) : r = a :=
  Check408.exact_accepted_result_is_unique408 p r a x y
    (accepted_implies_branch_engine408 p r x first) (accepted_implies_branch_engine408 p a y second)

theorem raw_closed_cycle_uses_the_same_checker408 (p : Problem) (r : Result)
    (w : GeneralDeclarativeWitnessCycle350.Wire) :
    check p r (.rawRoot w) = true ↔
      GeneralDeclarativeWitnessCycle350.check p.state.core.current.ordinary p.root.demand w = true ∧
      r = Check408.rawReport :=
  Check408.bool_raw_protocol_exact408 p r w

end Yulang.GeneralDeclarativeI65.I72.Checker408
