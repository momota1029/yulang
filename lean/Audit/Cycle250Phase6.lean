import Yulang.GeneralNominalStableCapture250
import Yulang.GeneralNominalStableCaptureStep250
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralNominalStableCapture250.bounds,
  ``Yulang.GeneralNominalStableCapture250.equation_value,
  ``Yulang.GeneralNominalStableCapture250.bound_values,
  ``Yulang.GeneralNominalStableCapture250.bounds_exact,
  ``Yulang.GeneralNominalStableCaptureStep250.next,
  ``Yulang.GeneralNominalStableCaptureStep250.generated_equations,
  ``Yulang.GeneralNominalStableCaptureStep250.snapshot_bounds_exact,
  ``Yulang.GeneralNominalStableCaptureStep250.actual_bounds_exact]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE250-PHASE6-PASS: {names.size} explicit declarations in 2 modules"
