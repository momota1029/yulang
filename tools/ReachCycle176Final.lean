import Yulang.GeneralDictionaryCenteredCandidate176
import Yulang.GeneralDictionaryCenteredFlexible176
import Yulang.GeneralDictionaryCenteredFootprint176
import Yulang.GeneralDictionaryCenteredInhabited176
import Yulang.GeneralDictionaryCenteredLedger176
import Yulang.GeneralDictionaryCenteredNonvacuous176
import Yulang.GeneralDictionaryCenteredReady176
import Yulang.GeneralDictionaryCenteredRecorded176
import Yulang.GeneralDictionaryCenteredRegression176
import Yulang.GeneralDictionaryCenteredRevision176
import Yulang.GeneralDictionaryCenteredSharedMerge176
import Yulang.GeneralDictionaryCenteredTree176
import Yulang.GeneralDictionaryHeadFootprintRegression176
import Yulang.GeneralDictionaryViewFootprint176
import Yulang.GeneralNominalCenteredGroundComposition
import Lean
/-!
Read-only declaration dependency closure. Run from lean/:
YULANG_REACH_ROOTS=/absolute/roots.txt YULANG_REACH_OUTPUT=/absolute/declarations.tsv \
  lake env lean ../tools/ReachCycle176.lean
Roots are full declaration names, one per line. The output includes every loaded
cycle176 declaration, its defining module, and whether it is reachable through
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
      if moduleName.toString.startsWith "Yulang.GeneralDictionary" && moduleName.toString.endsWith "176" then
        let yes := visited.contains name
        if yes then reached := reached + 1
        rows := rows.push s!"{moduleName}\t{name}\t{if yes then "1" else "0"}"
  let sorted := rows.qsort (· < ·)
  IO.FS.writeFile outputPath ("module\tdeclaration\treachable\n" ++ String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"REACH: {roots.length} roots; {reached}/{sorted.size} cycle176 declarations reachable"
