import Yulang.GeneralNominalPlanProducer251
import Yulang.GeneralNominalRegisteredPlan251
import Yulang.GeneralNominalPlanTrace251
import Yulang.GeneralNominalPlanTraceModels251
import Yulang.GeneralNominalPlanProducerRegression251
import Yulang.GeneralPresenceSnapshotGrowth251
import Yulang.GeneralPresenceDuplicateUnion251
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralNominalPlanProducer251.handle,
  ``Yulang.GeneralNominalPlanProducer251.opened,
  ``Yulang.GeneralNominalPlanProducer251.fallback,
  ``Yulang.GeneralNominalPlanProducer251.env,
  ``Yulang.GeneralNominalPlanProducer251.command,
  ``Yulang.GeneralNominalPlanProducer251.result,
  ``Yulang.GeneralNominalPlanProducer251.aligned,
  ``Yulang.GeneralNominalPlanProducer251.coverage,
  ``Yulang.GeneralNominalPlanProducer251.safe,
  ``Yulang.GeneralNominalPlanProducer251.needed_covered,
  ``Yulang.GeneralNominalPlanProducer251.checked_success,
  ``Yulang.GeneralNominalPlanProducer251.seedAssignment,
  ``Yulang.GeneralNominalPlanProducer251.finalAssignment,
  ``Yulang.GeneralNominalPlanProducer251.reference,
  ``Yulang.GeneralNominalPlanProducer251.install_exact,
  ``Yulang.GeneralNominalRegisteredPlan251.Matches,
  ``Yulang.GeneralNominalRegisteredPlan251.build,
  ``Yulang.GeneralNominalRegisteredPlan251.compile,
  ``Yulang.GeneralNominalRegisteredPlan251.compile_exact,
  ``Yulang.GeneralNominalRegisteredPlan251.compile_success,
  ``Yulang.GeneralNominalRegisteredPlan251.covered,
  ``Yulang.GeneralNominalRegisteredPlan251.checked_success,
  ``Yulang.GeneralNominalRegisteredPlan251.retains_registry,
  ``Yulang.GeneralNominalRegisteredPlan251.needed_covered,
  ``Yulang.GeneralNominalPlanTrace251.compile,
  ``Yulang.GeneralNominalPlanTrace251.covered,
  ``Yulang.GeneralNominalPlanTrace251.checked_success,
  ``Yulang.GeneralNominalPlanTrace251.Known,
  ``Yulang.GeneralNominalPlanTrace251.total_on_known,
  ``Yulang.GeneralNominalPlanTrace251.length_exact,
  ``Yulang.GeneralNominalPlanTrace251.fixed_targets,
  ``Yulang.GeneralNominalPlanTraceModels251.PlanHolds,
  ``Yulang.GeneralNominalPlanTraceModels251.condition_exact,
  ``Yulang.GeneralNominalPlanTraceModels251.Holds,
  ``Yulang.GeneralNominalPlanTraceModels251.permitted_exact,
  ``Yulang.GeneralNominalPlanTraceModels251.public_models_iff,
  ``Yulang.GeneralNominalPlanProducerRegression251.plan,
  ``Yulang.GeneralNominalPlanProducerRegression251.frame,
  ``Yulang.GeneralNominalPlanProducerRegression251.handle,
  ``Yulang.GeneralNominalPlanProducerRegression251.initial,
  ``Yulang.GeneralNominalPlanProducerRegression251.frame_safe,
  ``Yulang.GeneralNominalPlanProducerRegression251.initial_safe,
  ``Yulang.GeneralNominalPlanProducerRegression251.registered,
  ``Yulang.GeneralNominalPlanProducerRegression251.same_owner,
  ``Yulang.GeneralNominalPlanProducerRegression251.two_plans_compile,
  ``Yulang.GeneralNominalPlanProducerRegression251.no_unregistered_plan,
  ``Yulang.GeneralNominalPlanProducerRegression251.no_version_growth,
  ``Yulang.GeneralPresenceSnapshotGrowth251.tree,
  ``Yulang.GeneralPresenceSnapshotGrowth251.height,
  ``Yulang.GeneralPresenceSnapshotGrowth251.definitions,
  ``Yulang.GeneralPresenceSnapshotGrowth251.raw,
  ``Yulang.GeneralPresenceSnapshotGrowth251.height_tree,
  ``Yulang.GeneralPresenceSnapshotGrowth251.next_different,
  ``Yulang.GeneralPresenceSnapshotGrowth251.reads_zero,
  ``Yulang.GeneralPresenceSnapshotGrowth251.safe,
  ``Yulang.GeneralPresenceSnapshotGrowth251.refresh,
  ``Yulang.GeneralPresenceSnapshotGrowth251.fixed_target,
  ``Yulang.GeneralPresenceSnapshotGrowth251.no_uniform_height_bound,
  ``Yulang.GeneralPresenceSnapshotGrowth251.union_self,
  ``Yulang.GeneralPresenceSnapshotGrowth251.same_value,
  ``Yulang.GeneralPresenceDuplicateUnion251.reduce,
  ``Yulang.GeneralPresenceDuplicateUnion251.equivalent,
  ``Yulang.GeneralPresenceDuplicateUnion251.reads_subset,
  ``Yulang.GeneralPresenceDuplicateUnion251.entries,
  ``Yulang.GeneralPresenceDuplicateUnion251.safe,
  ``Yulang.GeneralPresenceDuplicateUnion251.equations_iff,
  ``Yulang.GeneralPresenceDuplicateUnion251.block_iff,
  ``Yulang.GeneralPresenceDuplicateUnion251.targets,
  ``Yulang.GeneralPresenceDuplicateUnion251.refresh,
  ``Yulang.GeneralPresenceDuplicateUnion251.refresh_safe,
  ``Yulang.GeneralPresenceDuplicateUnion251.duplication_fixed]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE251-PHASE3-PASS: {names.size} explicit declarations in 7 modules"
