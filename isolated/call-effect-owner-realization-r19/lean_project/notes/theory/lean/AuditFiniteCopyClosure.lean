import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.FiniteCopyClosure

/-! Complete originating-module audit, including private/generated theorems.
Run `lake build +YulangClosure.FiniteCopyClosure`, then
`lake env lean -j1 -M1024 AuditFiniteCopyClosure.lean`.
These are conditional finite-closure obstruction lemmas. Their Closed/Seed
premises have not been established for the native source execution. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
open Lean Elab Command

run_cmd do
  let moduleName := `YulangClosure.FiniteCopyClosure
  let roots : Array Name := #[
    `YulangClosure.FiniteCopyClosure.initial_copy,
    `YulangClosure.FiniteCopyClosure.anchored_copy_produces_newer,
    `YulangClosure.FiniteCopyClosure.arbitrarily_large_anchored_copy,
    `YulangClosure.FiniteCopyClosure.no_finite_copy_closure,
    `YulangClosure.FiniteCopyClosure.native_high_to_low_selects_parent_upper
  ]
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "audited module is not imported: {moduleName}"
  let mut targets : Array Name := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then
      match info with
      | .thmInfo _ => targets := targets.push name
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
  if targets.isEmpty then throwError "empty theorem inventory"
  for root in roots do
    unless targets.contains root do throwError "missing required theorem: {root}"
  for name in targets do
    logInfo m!"YULANG_AUDIT_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_AUDIT_END {name}"
  logInfo m!"YULANG_AUDIT_COUNT {targets.size}"
