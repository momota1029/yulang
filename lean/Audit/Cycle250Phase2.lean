import Yulang.GeneralNominalJournalAppend250
import Yulang.GeneralPresencePersistentSnapshot250
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralNominalJournalAppend250.Delta,
  ``Yulang.GeneralNominalJournalAppend250.Delta.Holds,
  ``Yulang.GeneralNominalJournalAppend250.appendJournal,
  ``Yulang.GeneralNominalJournalAppend250.attach,
  ``Yulang.GeneralNominalJournalAppend250.attach_models,
  ``Yulang.GeneralNominalJournalAppend250.subst,
  ``Yulang.GeneralNominalJournalAppend250.subst_exact,
  ``Yulang.GeneralNominalJournalAppend250.rebase_attach,
  ``Yulang.GeneralNominalJournalAppend250.snapshot_attach,
  ``Yulang.GeneralNominalJournalAppend250.augmented_public_models_iff,
  ``Yulang.GeneralPresencePersistentSnapshot250.overlay,
  ``Yulang.GeneralPresencePersistentSnapshot250.refresh,
  ``Yulang.GeneralPresencePersistentSnapshot250.target_list,
  ``Yulang.GeneralPresencePersistentSnapshot250.overlay_within,
  ``Yulang.GeneralPresencePersistentSnapshot250.refresh_within,
  ``Yulang.GeneralPresencePersistentSnapshot250.old_within,
  ``Yulang.GeneralPresencePersistentSnapshot250.safe_nodup,
  ``Yulang.GeneralPresencePersistentSnapshot250.refresh_safe,
  ``Yulang.GeneralPresencePersistentSnapshot250.lookup_coherent,
  ``Yulang.GeneralPresencePersistentSnapshot250.covers,
  ``Yulang.GeneralPresencePersistentSnapshot250.retains_missing,
  ``Yulang.GeneralPresencePersistentSnapshot250.raw_equations]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE250-PHASE2-PASS: {names.size} explicit declarations in 2 modules"
