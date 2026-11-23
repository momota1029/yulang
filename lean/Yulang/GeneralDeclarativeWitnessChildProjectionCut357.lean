import Yulang.GeneralDeclarativeWitnessGeneratedEndpoints357
import Yulang.GeneralDeclarativeWitnessReifiedViews357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 46000
set_option maxHeartbeats 53000000
namespace Yulang.GeneralDeclarativeWitnessChildProjectionCut357
open GeneralDeclarativeWitnessDeclaredState357 (Current Joined AuthoredNominal)
open GeneralDeclarativeWitnessReifiedViews357 (modelViews no_unsourced)
open GeneralDeclarativeWitnessGeneratedEndpoints357 (child cap child_not_point checked_link)
open GeneralDeclarativeWitnessJoinedFixture357 (Data data root)
open GeneralNominalCommonBridge (Assignment)

theorem compare_is_not_point_capture {s : Current} {impl} :
    ¬ Nonempty (Joined s child impl) := by
  rintro ⟨r⟩
  have here := List.cons.inj r.demanded
  have center := congrArg GeneralDeclarativeWhere319.Capture.center here.1
  have lower := congrArg GeneralDeclarativeWhere319.Capture.lower here.1
  exact child_not_point.1 (lower.trans center.symm)

def noEndpointSource (d : Data) : Bool :=
  d.current.visible.all fun row => decide (row.place ≠ cap.lower ∧ row.place ≠ cap.upper)

theorem actual_endpoints_not_literal_nominal_sources :
    ((data true).map noEndpointSource).getD false = true := by decide +kernel

theorem separate_provenance_needed {d : Data} (found : data true = some d)
    (m : Assignment) :
    (∀ row ∈ d.current.visible,row.place ≠ cap.lower ∧ row.place ≠ cap.upper) ∧
    modelViews d.current m cap.lower = none ∧ modelViews d.current m cap.upper = none := by
  have test := actual_endpoints_not_literal_nominal_sources
  rw [found] at test
  have each : ∀ row ∈ d.current.visible,row.place ≠ cap.lower ∧ row.place ≠ cap.upper :=
    fun row found => of_decide_eq_true (List.all_eq_true.mp (show noEndpointSource d = true from test) row found)
  refine ⟨each,?_,?_⟩
  · cases actual : modelViews d.current m cap.lower with
    | none => rfl
    | some a =>
      obtain ⟨row,there,same,_⟩ := no_unsourced actual
      exact False.elim ((each row there).1 same)
  · cases actual : modelViews d.current m cap.upper with
    | none => rfl
    | some a =>
      obtain ⟨row,there,same,_⟩ := no_unsourced actual
      exact False.elim ((each row there).2 same)

end Yulang.GeneralDeclarativeWitnessChildProjectionCut357
