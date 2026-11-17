import Yulang.GeneralNominalFiniteInstallTrace250
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralNominalFiniteInstallTrace250.Command,
  ``Yulang.GeneralNominalFiniteInstallTrace250.advance,
  ``Yulang.GeneralNominalFiniteInstallTrace250.nextAssignment,
  ``Yulang.GeneralNominalFiniteInstallTrace250.run,
  ``Yulang.GeneralNominalFiniteInstallTrace250.realize,
  ``Yulang.GeneralNominalFiniteInstallTrace250.Permitted,
  ``Yulang.GeneralNominalFiniteInstallTrace250.next_same,
  ``Yulang.GeneralNominalFiniteInstallTrace250.permitted_iff,
  ``Yulang.GeneralNominalFiniteInstallTrace250.targets_advance,
  ``Yulang.GeneralNominalFiniteInstallTrace250.targets_run,
  ``Yulang.GeneralNominalFiniteInstallTrace250.safe_advance,
  ``Yulang.GeneralNominalFiniteInstallTrace250.forward,
  ``Yulang.GeneralNominalFiniteInstallTrace250.realize_outside,
  ``Yulang.GeneralNominalFiniteInstallTrace250.backward,
  ``Yulang.GeneralNominalFiniteInstallTrace250.public_run_iff]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE250-PHASE4-PASS: {names.size} explicit declarations in 1 modules"
