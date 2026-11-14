import Yulang.GeneralDictionaryAgreedCompletion175
import Yulang.GeneralDictionaryAgreedTable175
import Yulang.GeneralDictionaryAgreedCertifiedEvidence175
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`Yulang.GeneralDictionaryAgreedCompletion175, `Yulang.GeneralDictionaryAgreedTable175, `Yulang.GeneralDictionaryAgreedCertifiedEvidence175]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      checked := checked + 1
      for dependency in ← collectAxioms name do
        unless allowed.contains dependency do
          throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
