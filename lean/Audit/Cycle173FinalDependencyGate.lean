import Yulang.GeneralDictionaryActualEdge173
import Yulang.GeneralDictionaryActualGroundExample173
import Yulang.GeneralDictionaryActualGroundComposition173
import Yulang.GeneralDictionaryActualGroundExecutor173
import Yulang.GeneralDictionaryActualRecorded173
import Yulang.GeneralDictionaryActualStable173
import Yulang.GeneralDictionaryActualV5173
import Yulang.GeneralDictionaryActualExample173
import Yulang.GeneralDictionary172CoverageSyntax
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`Yulang.GeneralDictionaryActualEdge173, `Yulang.GeneralDictionaryActualGroundExample173, `Yulang.GeneralDictionaryActualRecorded173, `Yulang.GeneralDictionaryActualStable173, `Yulang.GeneralDictionaryActualV5173, `Yulang.GeneralDictionaryActualExample173, `Yulang.GeneralDictionary172CoverageSyntax, `Yulang.GeneralDictionaryActualGroundExecutor173, `Yulang.GeneralDictionaryActualGroundComposition173]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      checked := checked + 1
      for dependency in ← collectAxioms name do
        unless allowed.contains dependency do
          throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
