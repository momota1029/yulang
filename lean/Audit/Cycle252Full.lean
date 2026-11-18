import Yulang.GeneralPresenceUnionNormal252
import Yulang.GeneralPresenceInterNormal252
import Yulang.GeneralPresenceNormalFinite252
import Yulang.GeneralPresenceSnapshotNormal252
import Yulang.GeneralPresenceCheckedNormal252
import Yulang.GeneralPresenceNormalBlock252
import Yulang.GeneralPresenceFiniteBlocks252
import Yulang.GeneralNominalOwnerCandidates252
import Yulang.GeneralNominalSourceOwnerCandidates252
import Yulang.GeneralDictionaryOutputDepth252
import Yulang.GeneralDictionaryOutputDepthCycles252
import Yulang.GeneralDictionaryOutputDepthInstall252
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralPresenceUnionNormal252.", "_private.Yulang.GeneralPresenceUnionNormal252.",
  "Yulang.GeneralPresenceInterNormal252.", "_private.Yulang.GeneralPresenceInterNormal252.",
  "Yulang.GeneralPresenceNormalFinite252.", "_private.Yulang.GeneralPresenceNormalFinite252.",
  "Yulang.GeneralPresenceSnapshotNormal252.", "_private.Yulang.GeneralPresenceSnapshotNormal252.",
  "Yulang.GeneralPresenceCheckedNormal252.", "_private.Yulang.GeneralPresenceCheckedNormal252.",
  "Yulang.GeneralPresenceNormalBlock252.", "_private.Yulang.GeneralPresenceNormalBlock252.",
  "Yulang.GeneralPresenceFiniteBlocks252.", "_private.Yulang.GeneralPresenceFiniteBlocks252.",
  "Yulang.GeneralNominalOwnerCandidates252.", "_private.Yulang.GeneralNominalOwnerCandidates252.",
  "Yulang.GeneralNominalSourceOwnerCandidates252.", "_private.Yulang.GeneralNominalSourceOwnerCandidates252.",
  "Yulang.GeneralDictionaryOutputDepth252.", "_private.Yulang.GeneralDictionaryOutputDepth252.",
  "Yulang.GeneralDictionaryOutputDepthCycles252.", "_private.Yulang.GeneralDictionaryOutputDepthCycles252.",
  "Yulang.GeneralDictionaryOutputDepthInstall252.", "_private.Yulang.GeneralDictionaryOutputDepthInstall252."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE252-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
