import Yulang.GeneralNominalOrderedSupport248
import Yulang.GeneralNominalOrderedMerge248
import Yulang.GeneralNominalOrderedInitial248
import Yulang.GeneralNominalOrderedRaw248
import Yulang.GeneralNominalOrderedLive248
import Yulang.GeneralNominalOrderedViewSyntax248
import Yulang.GeneralNominalOrderedOrigin248
import Yulang.GeneralNominalOrderedPacket248
import Yulang.GeneralNominalOrderedMergeExample248
import Yulang.GeneralNominalOrderedPacketModels248
import Yulang.GeneralNominalOrderedBundle248
import Yulang.GeneralNominalOrderedRefreshDomainLimit248
import Yulang.GeneralNominalOrderedRefreshPoolLimit248
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralNominalOrderedSupport248.row_sources,
  ``Yulang.GeneralNominalOrderedSupport248.type_sources,
  ``Yulang.GeneralNominalOrderedSupport248.typed_reads_subset,
  ``Yulang.GeneralNominalOrderedSupport248.safe_actual_pool,
  ``Yulang.GeneralNominalOrderedMerge248.entries,
  ``Yulang.GeneralNominalOrderedMerge248.coherent,
  ``Yulang.GeneralNominalOrderedMerge248.typed_supported,
  ``Yulang.GeneralNominalOrderedMerge248.prepared,
  ``Yulang.GeneralNominalOrderedMerge248.original_extension,
  ``Yulang.GeneralNominalOrderedMerge248.merges_of_entries,
  ``Yulang.GeneralNominalOrderedMerge248.actual_merge_extension,
  ``Yulang.GeneralNominalOrderedInitial248.input_key,
  ``Yulang.GeneralNominalOrderedInitial248.protected_of_new_keys,
  ``Yulang.GeneralNominalOrderedInitial248.first_propagation_model,
  ``Yulang.GeneralNominalOrderedRaw248.read_mapping,
  ``Yulang.GeneralNominalOrderedRaw248.raw_exact,
  ``Yulang.GeneralNominalOrderedRaw248.raw_forward,
  ``Yulang.GeneralNominalOrderedRaw248.raw_public_models_iff,
  ``Yulang.GeneralNominalOrderedLive248.site_compatible,
  ``Yulang.GeneralNominalOrderedLive248.site_forward,
  ``Yulang.GeneralNominalOrderedLive248.sites_forward,
  ``Yulang.GeneralNominalOrderedLive248.outputs_forward,
  ``Yulang.GeneralNominalOrderedLive248.role_identity,
  ``Yulang.GeneralNominalOrderedViewSyntax248.comp_absorbs,
  ``Yulang.GeneralNominalOrderedViewSyntax248.parameter_absorbs,
  ``Yulang.GeneralNominalOrderedViewSyntax248.descriptor_absorbs,
  ``Yulang.GeneralNominalOrderedViewSyntax248.atom_absorbs,
  ``Yulang.GeneralNominalOrderedViewSyntax248.view_absorbs,
  ``Yulang.GeneralNominalOrderedOrigin248.equiv_refl,
  ``Yulang.GeneralNominalOrderedOrigin248.equiv_symm,
  ``Yulang.GeneralNominalOrderedOrigin248.equiv_trans,
  ``Yulang.GeneralNominalOrderedOrigin248.compatible_symm,
  ``Yulang.GeneralNominalOrderedOrigin248.read_mapping,
  ``Yulang.GeneralNominalOrderedOrigin248.compile_ordered_exact,
  ``Yulang.GeneralNominalOrderedOrigin248.subst_ordered_exact,
  ``Yulang.GeneralNominalOrderedOrigin248.observes_transport,
  ``Yulang.GeneralNominalOrderedOrigin248.nominal_transport,
  ``Yulang.GeneralNominalOrderedOrigin248.structural_transport,
  ``Yulang.GeneralNominalOrderedOrigin248.nominal_iff,
  ``Yulang.GeneralNominalOrderedOrigin248.structural_iff,
  ``Yulang.GeneralNominalOrderedOrigin248.test_transport,
  ``Yulang.GeneralNominalOrderedOrigin248.test_iff,
  ``Yulang.GeneralNominalOrderedOrigin248.head_transport,
  ``Yulang.GeneralNominalOrderedOrigin248.head_iff,
  ``Yulang.GeneralNominalOrderedOrigin248.same_transport,
  ``Yulang.GeneralNominalOrderedOrigin248.same_iff,
  ``Yulang.GeneralNominalOrderedOrigin248.nominal_rebase,
  ``Yulang.GeneralNominalOrderedOrigin248.structural_rebase,
  ``Yulang.GeneralNominalOrderedOrigin248.head_rebase,
  ``Yulang.GeneralNominalOrderedOrigin248.same_rebase,
  ``Yulang.GeneralNominalOrderedOrigin248.observes_rebase_forward,
  ``Yulang.GeneralNominalOrderedOrigin248.observes_rebase_backward,
  ``Yulang.GeneralNominalOrderedPacket248.assignment_same,
  ``Yulang.GeneralNominalOrderedPacket248.projection_exact,
  ``Yulang.GeneralNominalOrderedPacket248.packet_exact,
  ``Yulang.GeneralNominalOrderedPacket248.projection_recovered,
  ``Yulang.GeneralNominalOrderedPacket248.packet_recovered,
  ``Yulang.GeneralNominalOrderedPacket248.projection_rebase,
  ``Yulang.GeneralNominalOrderedPacket248.packet_rebase,
  ``Yulang.GeneralNominalOrderedPacket248.packets_rebase,
  ``Yulang.GeneralNominalOrderedMergeExample248.bindings,
  ``Yulang.GeneralNominalOrderedMergeExample248.names,
  ``Yulang.GeneralNominalOrderedMergeExample248.pool,
  ``Yulang.GeneralNominalOrderedMergeExample248.lo,
  ``Yulang.GeneralNominalOrderedMergeExample248.hi,
  ``Yulang.GeneralNominalOrderedMergeExample248.protected_pool,
  ``Yulang.GeneralNominalOrderedMergeExample248.endpoints,
  ``Yulang.GeneralNominalOrderedMergeExample248.actual_entries,
  ``Yulang.GeneralNominalOrderedMergeExample248.repeated_input_prepares,
  ``Yulang.GeneralNominalOrderedMergeExample248.every_boundary_extends,
  ``Yulang.GeneralNominalOrderedPacketModels248.models_forward,
  ``Yulang.GeneralNominalOrderedPacketModels248.models_backward,
  ``Yulang.GeneralNominalOrderedPacketModels248.public_models_iff,
  ``Yulang.GeneralNominalOrderedBundle248.sites_exact,
  ``Yulang.GeneralNominalOrderedBundle248.public_models_iff,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.oldBindings,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.freshBindings,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.names,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.old,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.fresh,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.stable_slots,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.old_empty,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.fresh_entries,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.targets_not_within,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.old_prepares,
  ``Yulang.GeneralNominalOrderedRefreshDomainLimit248.fresh_prepares,
  ``Yulang.GeneralNominalOrderedRefreshPoolLimit248.slot_in_propagated_sources,
  ``Yulang.GeneralNominalOrderedRefreshPoolLimit248.not_full_pool_fresh]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE248-FINAL-PASS: {names.size} explicit source declarations in 13 modules"
