import Yulang.GeneralDictionaryAgreedComposition174
import Yulang.GeneralDictionaryAgreedEdge174
import Yulang.GeneralDictionaryAgreedEvidence174
import Yulang.GeneralDictionaryAgreedExact174
import Yulang.GeneralDictionaryAgreedGround174
import Yulang.GeneralDictionaryAgreedRoleExamples174
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`Yulang.GeneralDictionaryAgreedComposition174, `Yulang.GeneralDictionaryAgreedEdge174, `Yulang.GeneralDictionaryAgreedEvidence174, `Yulang.GeneralDictionaryAgreedExact174, `Yulang.GeneralDictionaryAgreedGround174, `Yulang.GeneralDictionaryAgreedRoleExamples174]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      checked := checked + 1
      for dependency in ← collectAxioms name do
        unless allowed.contains dependency do
          throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
