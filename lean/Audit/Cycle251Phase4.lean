import Yulang.GeneralNominalRoleEffects251
import Yulang.GeneralNominalRoleClass251
import Yulang.GeneralNominalRoleClassCompleteness251
import Yulang.GeneralNominalRoleJournalEffect251
import Yulang.GeneralNominalRoleModeRegression251
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralNominalRoleEffects251.variables,
  ``Yulang.GeneralNominalRoleEffects251.values,
  ``Yulang.GeneralNominalRoleEffects251.variables_exact,
  ``Yulang.GeneralNominalRoleEffects251.compileBody,
  ``Yulang.GeneralNominalRoleEffects251.OutputHolds,
  ``Yulang.GeneralNominalRoleEffects251.compile,
  ``Yulang.GeneralNominalRoleEffects251.output_exact,
  ``Yulang.GeneralNominalRoleEffects251.compiled_exact,
  ``Yulang.GeneralNominalRoleClass251.equations,
  ``Yulang.GeneralNominalRoleClass251.equations_exact,
  ``Yulang.GeneralNominalRoleClass251.compile,
  ``Yulang.GeneralNominalRoleClass251.Holds,
  ``Yulang.GeneralNominalRoleClass251.compile_exact,
  ``Yulang.GeneralNominalRoleClass251.current,
  ``Yulang.GeneralNominalRoleClass251.current_exact,
  ``Yulang.GeneralNominalRoleClass251.equations_length,
  ``Yulang.GeneralNominalRoleClassCompleteness251.equations_complete,
  ``Yulang.GeneralNominalRoleClassCompleteness251.model_exact,
  ``Yulang.GeneralNominalRoleJournalEffect251.assemble,
  ``Yulang.GeneralNominalRoleJournalEffect251.compile,
  ``Yulang.GeneralNominalRoleJournalEffect251.Holds,
  ``Yulang.GeneralNominalRoleJournalEffect251.assemble_exact,
  ``Yulang.GeneralNominalRoleJournalEffect251.compile_exact,
  ``Yulang.GeneralNominalRoleJournalEffect251.model_exact,
  ``Yulang.GeneralNominalRoleJournalEffect251.delta,
  ``Yulang.GeneralNominalRoleJournalEffect251.delta_exact,
  ``Yulang.GeneralNominalRoleModeRegression251.equation,
  ``Yulang.GeneralNominalRoleModeRegression251.positional_default_valid,
  ``Yulang.GeneralNominalRoleModeRegression251.named_explicit_invalid,
  ``Yulang.GeneralNominalRoleModeRegression251.nominal_arguments_actual,
  ``Yulang.GeneralNominalRoleModeRegression251.output_overrides_lower,
  ``Yulang.GeneralNominalRoleModeRegression251.unknownRequest,
  ``Yulang.GeneralNominalRoleModeRegression251.unknown_flag,
  ``Yulang.GeneralNominalRoleModeRegression251.unknown_equations_empty,
  ``Yulang.GeneralNominalRoleModeRegression251.unknown_holds_vacuously,
  ``Yulang.GeneralNominalRoleModeRegression251.unknown_not_known]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE251-PHASE4-PASS: {names.size} explicit declarations in 5 modules"
