import Yulang.GeneralDeclarativeI65I72GroundedLocalReceipt405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)

def literalVariablePosition405 (row i : Nat) : Pattern → Option VariablePosition405
  | .var n => some ⟨row,i,n⟩
  | _ => none

/-- Canonical literal positions, independently of any candidate proof.
This display projection is not a matcher: non-variable written syntax
is deliberately not assigned a classification by it. -/
def literalVariablePositions405 : List Declaration → Nat → List VariablePosition405
  | [], _ => []
  | row::rows, i => ((row.head.mapIdx (literalVariablePosition405 i)).filterMap id) ++
      literalVariablePositions405 rows (i+1)

private theorem variable_position_literal_batch405 (ns : List Nat) (row start : Nat) :
    (((ns.map Pattern.var).zipIdx start).map (fun x => literalVariablePosition405 row x.2 x.1)).filterMap id =
      (ns.zipIdx start).map (fun x => ⟨row,x.2,x.1⟩) := by
  induction ns generalizing start with
  | nil => rfl
  | cons n rest ih =>
    rw [List.map_cons,List.zipIdx_cons,List.zipIdx_cons,List.map_cons,List.map_cons]
    change (some (⟨row,start,n⟩ : VariablePosition405) :: _).filterMap id = (⟨row,start,n⟩ : VariablePosition405) :: _
    rw [List.filterMap_cons_some (by rfl),ih]

theorem actual_variable_scan_is_canonical405 {s : State} {q rows}
    {t : CandidateTape s.core q rows} (scan : VariableScan405 t) (i : Nat) :
    scan.positions i = literalVariablePositions405 rows i := by
  induction scan generalizing i with
  | nil => rfl
  | @matched row rows tail pick inputs later ih =>
    rw [VariableScan405.positions,literalVariablePositions405,inputs.literal,ih]
    congr 1
    rw [List.mapIdx_eq_zipIdx_map,List.mapIdx_eq_zipIdx_map]
    exact (variable_position_literal_batch405 inputs.binders i 0).symm

/-- Changing the proof object or the capture/read term at the same
event does not change the derived *address order*. Comparison and
output meaning are still tied to the original event separately. -/
theorem no_selection_proof_can_append_an_unvisited_site405 {R s q e needs support}
    (a b : GroundedSelection405 (s := s) (q := q) R e needs support) :
    a.scan.positions = b.scan.positions ∧ a.scan.visits = b.scan.visits := by
  exact ⟨(actual_variable_scan_is_canonical405 a.scan 0).trans
    (actual_variable_scan_is_canonical405 b.scan 0).symm,
    (variable_scan_visits_exact405 a.scan).trans (variable_scan_visits_exact405 b.scan).symm⟩

/-- C404's inserted marker is still possible in the original record,
but cannot be produced by a grounded erasure on that exact selection.
This is the repair of the contradiction, not a theorem about every
language rule or every source receiver. -/
theorem inserted_marker_is_not_grounded405 {R s q e needs support}
    (a : GroundedSelection405 (s := s) (q := q) R e needs support) (marker : CandidateVisit) :
    ¬ ∃ b : GroundedSelection405 (s := s) (q := q) R e needs support,
      b.toSelectedSource = { a.toSelectedSource with visits := [marker] } := by
  rintro ⟨b,same⟩
  have visits := congrArg SelectedSource.visits same
  change b.scan.visits = [marker] at visits
  rw [variable_scan_visits_exact405 b.scan] at visits
  cases visits

end Yulang.GeneralDeclarativeI65.I72
