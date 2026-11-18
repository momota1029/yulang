import Yulang.GeneralNominalRawFinite253
import Yulang.GeneralNominalPublicPorts253
import Yulang.GeneralDictionaryCompoundPool253
import Yulang.GeneralDictionaryCompoundPoolRepair253
import Yulang.GeneralPatternDependencyDepth253
import Yulang.GeneralDictionaryOutputDepthRepair253
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralNominalRawFinite253.combine,
  ``Yulang.GeneralNominalRawFinite253.combine_mem,
  ``Yulang.GeneralNominalRawFinite253.choices,
  ``Yulang.GeneralNominalRawFinite253.manyChoices,
  ``Yulang.GeneralNominalRawFinite253.compile_mem,
  ``Yulang.GeneralNominalRawFinite253.compileMany_mem,
  ``Yulang.GeneralNominalRawFinite253.templateChoices,
  ``Yulang.GeneralNominalRawFinite253.template_mem,
  ``Yulang.GeneralNominalRawFinite253.opaque_reference_mem,
  ``Yulang.GeneralNominalRawFinite253.combine_count,
  ``Yulang.GeneralNominalRawFinite253.variableCount,
  ``Yulang.GeneralNominalRawFinite253.variableCounts,
  ``Yulang.GeneralNominalRawFinite253.choices_count,
  ``Yulang.GeneralNominalRawFinite253.manyChoices_count,
  ``Yulang.GeneralNominalPublicPorts253.ports,
  ``Yulang.GeneralNominalPublicPorts253.names,
  ``Yulang.GeneralNominalPublicPorts253.port_mem,
  ``Yulang.GeneralNominalPublicPorts253.output_mem,
  ``Yulang.GeneralNominalPublicPorts253.argument_mem,
  ``Yulang.GeneralNominalPublicPorts253.clause_output_mem,
  ``Yulang.GeneralNominalPublicPorts253.port_purpose,
  ``Yulang.GeneralNominalPublicPorts253.aggregate_not_port,
  ``Yulang.GeneralNominalPublicPorts253.aggregate_not_names,
  ``Yulang.GeneralNominalPublicPorts253.installed_port_enumerated,
  ``Yulang.GeneralNominalPublicPorts253.mixed_finite_ports,
  ``Yulang.GeneralDictionaryCompoundPool253.signature,
  ``Yulang.GeneralDictionaryCompoundPool253.site,
  ``Yulang.GeneralDictionaryCompoundPool253.endpoint,
  ``Yulang.GeneralDictionaryCompoundPool253.no_named_outputs,
  ``Yulang.GeneralDictionaryCompoundPool253.pool,
  ``Yulang.GeneralDictionaryCompoundPool253.endpoint_allocated,
  ``Yulang.GeneralDictionaryCompoundPool253.endpoint_new,
  ``Yulang.GeneralDictionaryCompoundPool253.endpoint_not_pool,
  ``Yulang.GeneralDictionaryCompoundPool253.emitted,
  ``Yulang.GeneralDictionaryCompoundPool253.site_reached,
  ``Yulang.GeneralDictionaryCompoundPool253.point_step,
  ``Yulang.GeneralDictionaryCompoundPool253.point_reachable,
  ``Yulang.GeneralDictionaryCompoundPool253.private_rewrite_unsupported,
  ``Yulang.GeneralDictionaryCompoundPool253.source_reachable_pool_gap,
  ``Yulang.GeneralDictionaryCompoundPoolRepair253.endpoint_in_ports,
  ``Yulang.GeneralDictionaryCompoundPoolRepair253.endpoint_in_names,
  ``Yulang.GeneralDictionaryCompoundPoolRepair253.repaired_atomic_support,
  ``Yulang.GeneralDictionaryCompoundPoolRepair253.pool_gap_and_local_repair,
  ``Yulang.GeneralPatternDependencyDepth253.Build,
  ``Yulang.GeneralPatternDependencyDepth253.sum_bound,
  ``Yulang.GeneralPatternDependencyDepth253.lengths,
  ``Yulang.GeneralPatternDependencyDepth253.sum_le_uniform,
  ``Yulang.GeneralPatternDependencyDepth253.uniform_bound,
  ``Yulang.GeneralPatternDependencyDepth253.no_positive_cycle,
  ``Yulang.GeneralPatternDependencyDepth253.alias_cycle_possible,
  ``Yulang.GeneralDictionaryOutputDepthRepair253.newDepth,
  ``Yulang.GeneralDictionaryOutputDepthRepair253.sharp,
  ``Yulang.GeneralDictionaryOutputDepthRepair253.additive,
  ``Yulang.GeneralDictionaryOutputDepthRepair253.source_reachable_additive_repair]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE253-PHASE2-PASS: {names.size} explicit declarations in 6 modules"
