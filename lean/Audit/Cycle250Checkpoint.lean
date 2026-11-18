import Yulang.GeneralPresenceSnapshotBlock250
import Yulang.GeneralNominalSnapshotOwner250
import Yulang.GeneralNominalSnapshotMerge250
import Yulang.GeneralNominalViewCongruence250
import Yulang.GeneralNominalOriginViewCongruence250
import Yulang.GeneralNominalProjectionViewCongruence250
import Yulang.GeneralNominalSchemaViewCongruence250
import Yulang.GeneralNominalExprViewCongruence250
import Yulang.GeneralNominalJournalViewCongruence250
import Yulang.GeneralNominalArbitraryOwnerFrame250
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralPresenceSnapshotBlock250.refresh,
  ``Yulang.GeneralPresenceSnapshotBlock250.transformed_within,
  ``Yulang.GeneralPresenceSnapshotBlock250.refresh_within,
  ``Yulang.GeneralPresenceSnapshotBlock250.transformed_closed,
  ``Yulang.GeneralPresenceSnapshotBlock250.refresh_safe,
  ``Yulang.GeneralPresenceSnapshotBlock250.transformed_coherent,
  ``Yulang.GeneralPresenceSnapshotBlock250.refresh_models,
  ``Yulang.GeneralPresenceSnapshotBlock250.rhs_snapshot,
  ``Yulang.GeneralNominalSnapshotOwner250.Block,
  ``Yulang.GeneralNominalSnapshotOwner250.update,
  ``Yulang.GeneralNominalSnapshotOwner250.update_formed,
  ``Yulang.GeneralNominalSnapshotOwner250.update_within,
  ``Yulang.GeneralNominalSnapshotOwner250.public_models_iff,
  ``Yulang.GeneralNominalSnapshotOwner250.exact_original_constraints,
  ``Yulang.GeneralNominalSnapshotMerge250.updateMerge,
  ``Yulang.GeneralNominalSnapshotMerge250.merge_formed,
  ``Yulang.GeneralNominalSnapshotMerge250.merge_public_models_iff,
  ``Yulang.GeneralNominalSnapshotMerge250.merge_exact,
  ``Yulang.GeneralNominalViewCongruence250.equiv_trans,
  ``Yulang.GeneralNominalViewCongruence250.equiv_iff,
  ``Yulang.GeneralNominalViewCongruence250.fits_iff,
  ``Yulang.GeneralNominalViewCongruence250.fitsAll,
  ``Yulang.GeneralNominalViewCongruence250.denotes_iff,
  ``Yulang.GeneralNominalViewCongruence250.models_iff,
  ``Yulang.GeneralNominalOriginViewCongruence250.observes,
  ``Yulang.GeneralNominalOriginViewCongruence250.inhabited_iff,
  ``Yulang.GeneralNominalOriginViewCongruence250.test_iff,
  ``Yulang.GeneralNominalOriginViewCongruence250.head,
  ``Yulang.GeneralNominalOriginViewCongruence250.head_iff,
  ``Yulang.GeneralNominalOriginViewCongruence250.shared,
  ``Yulang.GeneralNominalOriginViewCongruence250.shared_iff,
  ``Yulang.GeneralNominalProjectionViewCongruence250.fits_iff,
  ``Yulang.GeneralNominalProjectionViewCongruence250.projection,
  ``Yulang.GeneralNominalProjectionViewCongruence250.projection_iff,
  ``Yulang.GeneralNominalSchemaViewCongruence250.argument_iff,
  ``Yulang.GeneralNominalSchemaViewCongruence250.site_iff,
  ``Yulang.GeneralNominalSchemaViewCongruence250.requirement_iff,
  ``Yulang.GeneralNominalSchemaViewCongruence250.use_forward,
  ``Yulang.GeneralNominalSchemaViewCongruence250.use_iff,
  ``Yulang.GeneralNominalSchemaViewCongruence250.schema_iff,
  ``Yulang.GeneralNominalExprViewCongruence250.eval_equivalent,
  ``Yulang.GeneralNominalExprViewCongruence250.evals_equivalent,
  ``Yulang.GeneralNominalExprViewCongruence250.equation_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.equations_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.child_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.packet_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.class_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.effect_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.observed_forward,
  ``Yulang.GeneralNominalJournalViewCongruence250.observed_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.observations_iff,
  ``Yulang.GeneralNominalJournalViewCongruence250.models_iff,
  ``Yulang.GeneralNominalArbitraryOwnerFrame250.recovered,
  ``Yulang.GeneralNominalArbitraryOwnerFrame250.models_forward,
  ``Yulang.GeneralNominalArbitraryOwnerFrame250.public_models_iff,
  ``Yulang.GeneralNominalArbitraryOwnerFrame250.snapshot_public_models_iff]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE250-CHECKPOINT-PASS: {names.size} explicit declarations in 10 modules"
