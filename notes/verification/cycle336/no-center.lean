import Yulang.GeneralDeclarativeEndpointChildModels336
import Yulang.GeneralDeclarativeEndpointRegression336
import Yulang.GeneralDeclarativeEndpointResidualFixture336

namespace C336Replay
open Yulang
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction backed_iff)
open GeneralDeclarativeWitnessCutDecl334 (arg)

private theorem kept_right_shadow :
    (GeneralDeclarativeEndpointChildren336.final.equations.all
      (fun row => decide (row.left ≠ arg.center))) = true := by decide +kernel

/-- Replaying both actual compiler writes and endpoint support
materialization did not append any literal parent center row. -/
theorem selected_tree_no_literal_center {row : Equation}
    (present : row ∈ (restriction GeneralDeclarativeEndpointChildren336.authorized).equations) :
    row.left ≠ arg.center := by
  obtain ⟨o,origin,_⟩ := (backed_iff _ _).mp present
  have ordinary := GeneralDeclarativeEndpointChildren336.authorized.ordinary origin
  exact of_decide_eq_true (List.all_eq_true.mp kept_right_shadow row ordinary)

theorem exact_writes :
    GeneralDeclarativeEndpointChildren336.rootWrite.left = 6 ∧
    GeneralDeclarativeEndpointChildren336.rootWrite.right = .variable 11 ∧
    GeneralDeclarativeEndpointChildren336.childWrite.left = 5 ∧
    GeneralDeclarativeEndpointChildren336.childWrite.right = .variable 8 :=
  ⟨rfl,rfl,rfl,rfl⟩

#print axioms selected_tree_no_literal_center
#print axioms exact_writes
end C336Replay
