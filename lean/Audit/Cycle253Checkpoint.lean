import Yulang.GeneralPatternAdditiveDepth253
import Yulang.GeneralNominalExprDepth253
import Yulang.GeneralNominalOutputNames253
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralPatternAdditiveDepth253.depth,
  ``Yulang.GeneralPatternAdditiveDepth253.depths,
  ``Yulang.GeneralPatternAdditiveDepth253.subst_depth,
  ``Yulang.GeneralPatternAdditiveDepth253.subst_depths,
  ``Yulang.GeneralPatternAdditiveDepth253.rename_depth,
  ``Yulang.GeneralPatternAdditiveDepth253.rename_depths,
  ``Yulang.GeneralPatternAdditiveDepth253.member_depth,
  ``Yulang.GeneralPatternAdditiveDepth253.substitution_from_pool,
  ``Yulang.GeneralPatternAdditiveDepth253.tower,
  ``Yulang.GeneralPatternAdditiveDepth253.tower_depth,
  ``Yulang.GeneralPatternAdditiveDepth253.tower_subst,
  ``Yulang.GeneralPatternAdditiveDepth253.additive_bound_sharp,
  ``Yulang.GeneralNominalExprDepth253.Raw,
  ``Yulang.GeneralNominalExprDepth253.Materialized,
  ``Yulang.GeneralNominalExprDepth253.typeDepth,
  ``Yulang.GeneralNominalExprDepth253.rawDepth,
  ``Yulang.GeneralNominalExprDepth253.rawDepths,
  ``Yulang.GeneralNominalExprDepth253.materializedDepth,
  ``Yulang.GeneralNominalExprDepth253.materializedDepths,
  ``Yulang.GeneralNominalExprDepth253.compile_depth,
  ``Yulang.GeneralNominalExprDepth253.compile_depths,
  ``Yulang.GeneralNominalExprDepth253.reference_depth,
  ``Yulang.GeneralNominalExprDepth253.reference_depths,
  ``Yulang.GeneralNominalOutputNames253.outputs,
  ``Yulang.GeneralNominalOutputNames253.output_mem,
  ``Yulang.GeneralNominalOutputNames253.installed_output_enumerated,
  ``Yulang.GeneralNominalOutputNames253.mixed_finite_outputs,
  ``Yulang.GeneralNominalOutputNames253.point_finite_outputs]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE253-CHECKPOINT-PASS: {names.size} explicit declarations in 3 modules"
