import Yulang.GeneralPresenceUnionNormal252
import Yulang.GeneralPresenceInterNormal252
import Yulang.GeneralPresenceNormalFinite252
import Yulang.GeneralPresenceSnapshotNormal252
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralPresenceUnionNormal252.atoms,
  ``Yulang.GeneralPresenceUnionNormal252.fold,
  ``Yulang.GeneralPresenceUnionNormal252.canonical,
  ``Yulang.GeneralPresenceUnionNormal252.normalize,
  ``Yulang.GeneralPresenceUnionNormal252.atoms_nonempty,
  ``Yulang.GeneralPresenceUnionNormal252.atoms_flat,
  ``Yulang.GeneralPresenceUnionNormal252.canonical_mem,
  ``Yulang.GeneralPresenceUnionNormal252.canonical_exact,
  ``Yulang.GeneralPresenceUnionNormal252.canonical_nonempty,
  ``Yulang.GeneralPresenceUnionNormal252.fold_exact,
  ``Yulang.GeneralPresenceUnionNormal252.atoms_exact,
  ``Yulang.GeneralPresenceUnionNormal252.equivalent,
  ``Yulang.GeneralPresenceUnionNormal252.atoms_fold,
  ``Yulang.GeneralPresenceUnionNormal252.canonical_idempotent,
  ``Yulang.GeneralPresenceUnionNormal252.idempotent,
  ``Yulang.GeneralPresenceUnionNormal252.fold_reads,
  ``Yulang.GeneralPresenceUnionNormal252.no_private_reads,
  ``Yulang.GeneralPresenceUnionNormal252.canonical_nodup,
  ``Yulang.GeneralPresenceUnionNormal252.fold_all_reads,
  ``Yulang.GeneralPresenceUnionNormal252.no_private_all_reads,
  ``Yulang.GeneralPresenceInterNormal252.atoms,
  ``Yulang.GeneralPresenceInterNormal252.fold,
  ``Yulang.GeneralPresenceInterNormal252.canonical,
  ``Yulang.GeneralPresenceInterNormal252.normalize,
  ``Yulang.GeneralPresenceInterNormal252.atoms_nonempty,
  ``Yulang.GeneralPresenceInterNormal252.atoms_flat,
  ``Yulang.GeneralPresenceInterNormal252.canonical_mem,
  ``Yulang.GeneralPresenceInterNormal252.canonical_exact,
  ``Yulang.GeneralPresenceInterNormal252.canonical_nonempty,
  ``Yulang.GeneralPresenceInterNormal252.fold_exact,
  ``Yulang.GeneralPresenceInterNormal252.atoms_exact,
  ``Yulang.GeneralPresenceInterNormal252.equivalent,
  ``Yulang.GeneralPresenceInterNormal252.atoms_fold,
  ``Yulang.GeneralPresenceInterNormal252.canonical_idempotent,
  ``Yulang.GeneralPresenceInterNormal252.idempotent,
  ``Yulang.GeneralPresenceInterNormal252.fold_reads,
  ``Yulang.GeneralPresenceInterNormal252.no_private_reads,
  ``Yulang.GeneralPresenceInterNormal252.canonical_nodup,
  ``Yulang.GeneralPresenceInterNormal252.fold_all_reads,
  ``Yulang.GeneralPresenceInterNormal252.no_private_all_reads,
  ``Yulang.GeneralPresenceNormalFinite252.subsets,
  ``Yulang.GeneralPresenceNormalFinite252.selected_enumerated,
  ``Yulang.GeneralPresenceNormalFinite252.subsets_length,
  ``Yulang.GeneralPresenceNormalFinite252.lowerCandidates,
  ``Yulang.GeneralPresenceNormalFinite252.upperCandidates,
  ``Yulang.GeneralPresenceNormalFinite252.lower_enumerated,
  ``Yulang.GeneralPresenceNormalFinite252.upper_enumerated,
  ``Yulang.GeneralPresenceNormalFinite252.lower_count,
  ``Yulang.GeneralPresenceNormalFinite252.upper_count,
  ``Yulang.GeneralPresenceNormalFinite252.union_atoms_same,
  ``Yulang.GeneralPresenceNormalFinite252.intersection_atoms_same,
  ``Yulang.GeneralPresenceNormalFinite252.duplicated_tree_atoms,
  ``Yulang.GeneralPresenceNormalFinite252.duplicated_tree_fixed,
  ``Yulang.GeneralPresenceNormalFinite252.duplicate_union_fixed,
  ``Yulang.GeneralPresenceNormalFinite252.duplicate_inter_fixed,
  ``Yulang.GeneralPresenceSnapshotNormal252.union_subst_atoms,
  ``Yulang.GeneralPresenceSnapshotNormal252.inter_subst_atoms,
  ``Yulang.GeneralPresenceSnapshotNormal252.union_subst_supported,
  ``Yulang.GeneralPresenceSnapshotNormal252.inter_subst_supported,
  ``Yulang.GeneralPresenceSnapshotNormal252.lower,
  ``Yulang.GeneralPresenceSnapshotNormal252.upper,
  ``Yulang.GeneralPresenceSnapshotNormal252.lower_exact,
  ``Yulang.GeneralPresenceSnapshotNormal252.upper_exact,
  ``Yulang.GeneralPresenceSnapshotNormal252.lower_finite,
  ``Yulang.GeneralPresenceSnapshotNormal252.upper_finite]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE252-CHECKPOINT-PASS: {names.size} explicit declarations in 4 modules"
