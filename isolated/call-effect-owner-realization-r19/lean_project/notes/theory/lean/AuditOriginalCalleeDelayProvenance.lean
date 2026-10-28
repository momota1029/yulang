import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalCalleeDelayProvenance

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
open Lean Elab Command

/- Author-owned mechanical census; no independent-review claim. All module
constants, including generated constants, get full types and transitive axioms. -/
run_cmd do
  let env ← getEnv
  let some index := env.getModuleIdx? `YulangClosure.OriginalCalleeDelayProvenance
    | throwError "target module is not imported"
  let mut count : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some index then
      count := count + 1
      match info with
      | .thmInfo _ => theorems := theorems + 1
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
      logInfo m!"YULANG_CALLEE_DELAY_BEGIN {name}"
      let id := mkIdent name
      elabCommand (← `(#check @$id))
      elabCommand (← `(#print axioms $id))
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "unapproved axiom in {name}: {ax}"
      logInfo m!"YULANG_CALLEE_DELAY_END {name}"
  unless count > 0 do throwError "empty census"
  logInfo m!"YULANG_CALLEE_DELAY_COUNT declarations={count} theorems={theorems}"
