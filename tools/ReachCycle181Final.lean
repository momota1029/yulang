import Yulang.GeneralDictionaryCenteredAliasProvenance181
import Yulang.GeneralDictionaryCenteredLedger181
import Yulang.GeneralDictionaryCenteredLedgerExample181
import Yulang.GeneralDictionaryCenteredOverlapExact181
import Yulang.GeneralDictionaryCenteredProvenance181
import Yulang.GeneralNominalBinderIdentity181
import Yulang.GeneralNominalFramedExtension181
import Yulang.GeneralNominalLedgerReadback181
import Yulang.GeneralNominalModeExtension181
import Yulang.GeneralNominalModeFrame181
import Yulang.GeneralNominalModeFrameExample181
import Yulang.GeneralNominalModeLedger181
import Yulang.GeneralNominalObservationExtension181
import Yulang.GeneralNominalOriginAlias181
import Yulang.GeneralNominalOriginAliasExample181
import Yulang.GeneralNominalOriginRootAlias181
import Yulang.GeneralNominalSemanticCollisionExample181
import Yulang.GeneralNominalSemanticCompatibility181
import Yulang.GeneralNominalCenteredGroundComposition
import Lean
/-!
Read-only declaration dependency closure. Run from lean/:
YULANG_REACH_ROOTS=/absolute/roots.txt YULANG_REACH_OUTPUT=/absolute/declarations.tsv \
  lake env lean ../tools/ReachCycle181.lean
Roots are full declaration names, one per line. The output includes every loaded
cycle181 declaration, its defining module, and whether it is reachable through
constant types or values (opaque proof bodies included). No pruning is performed.
This is syntactic kernel dependency, not a test of specification relevance.
-/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let some rootPath ← IO.getEnv "YULANG_REACH_ROOTS"
    | throwError "REACH: set YULANG_REACH_ROOTS to an explicit roots file"
  let some outputPath ← IO.getEnv "YULANG_REACH_OUTPUT"
    | throwError "REACH: set YULANG_REACH_OUTPUT to a new report path"
  let input ← IO.FS.readFile rootPath
  let roots := input.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else some line.toName
  if roots.isEmpty then throwError "REACH: empty root set"
  for root in roots do
    unless environment.contains root do
      throwError "REACH: missing root {root}"
  let mut visited : NameSet := {}
  let mut pending := roots
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless visited.contains name do
      visited := visited.insert name
      if let some info := environment.find? name then
        pending := info.type.getUsedConstants.toList ++ pending
        if let some value := info.value? (allowOpaque := true) then
          pending := value.getUsedConstants.toList ++ pending
  let mut rows : Array String := #[]
  let mut reached : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "181" then
        let yes := visited.contains name
        if yes then reached := reached + 1
        rows := rows.push s!"{moduleName}\t{name}\t{if yes then "1" else "0"}"
  let sorted := rows.qsort (· < ·)
  IO.FS.writeFile outputPath ("module\tdeclaration\treachable\n" ++ String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"REACH: {roots.length} roots; {reached}/{sorted.size} cycle181 declarations reachable"
