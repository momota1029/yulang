import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalRecursiveClosure
/-! Complete originating-module type and axiom audit. The module constructs
canonical raw formal-return evidence; full typed admission, faithful witness
representation and original source membership remain separate obligations.
Build `+YulangClosure.OriginalRecursiveClosure` before running this file. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs false
set_option pp.maxSteps 1000000
open Lean Elab Command
run_cmd do
  let moduleName := `YulangClosure.OriginalRecursiveClosure
  let roots : Array Name := #[
    `YulangClosure.OriginalRecursiveClosure.registered_formal,
    `YulangClosure.OriginalRecursiveClosure.lambda_formal_registered,
    `YulangClosure.OriginalRecursiveClosure.formal_return_key_fields,
    `YulangClosure.OriginalRecursiveClosure.completed_return_retained,
    `YulangClosure.OriginalRecursiveClosure.pending_return_no_retained,
    `YulangClosure.OriginalRecursiveClosure.retained_is_completed,
    `YulangClosure.OriginalRecursiveClosure.completed_return_shared_anchor,
    `YulangClosure.OriginalRecursiveClosure.logical_frame_keeps_return_key,
    `YulangClosure.OriginalRecursiveClosure.every_old_anchor_preserved,
    `YulangClosure.OriginalRecursiveClosure.empty_frame_paths,
    `YulangClosure.OriginalRecursiveClosure.extend_frame_paths,
    `YulangClosure.OriginalRecursiveClosure.completed_return_key_fresh,
    `YulangClosure.OriginalRecursiveClosure.actual_return_shared_frames,
    `YulangClosure.OriginalRecursiveClosure.every_source_formal_return,
    `YulangClosure.OriginalRecursiveClosure.decode_computed_formal_shared,
    `YulangClosure.OriginalRecursiveClosure.prefix_original_strategy,
    `YulangClosure.OriginalRecursiveClosure.canonical_anchors_idempotent,
    `YulangClosure.OriginalRecursiveClosure.canonical_prefix_already_fixed
  ]
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "module not imported: {moduleName}"
  let mut targets : Array Name := #[]
  let mut theorems : Array Name := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then
      targets := targets.push name
      match info with
      | .thmInfo _ => theorems := theorems.push name
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
  if targets.isEmpty then throwError "empty originating inventory"
  for root in roots do
    unless theorems.contains root do
      throwError "required root is not an originating theorem: {root}"
  for name in targets do
    logInfo m!"CLOSURE_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"CLOSURE_END {name}"
  logInfo m!"CLOSURE_CENSUS declarations={targets.size} theorems={theorems.size} publicRoots={roots.size}"
