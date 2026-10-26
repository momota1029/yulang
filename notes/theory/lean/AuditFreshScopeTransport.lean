import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.NativeFreshScopeTransport

/-! Complete originating-module audit, including private/generated theorems.
Run `lake build +YulangClosure.NativeFreshScopeTransport`, then
`lake env lean -j1 -M1024 AuditFreshScopeTransport.lean`.
The checker validates the stated allocation projection; it does not certify
source-to-inventory correspondence or full Rust execution. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
open Lean Elab Command

run_cmd do
  let moduleName := `YulangClosure.NativeFreshScopeTransport
  let roots : Array Name := #[
    `YulangClosure.NativeFreshScopeTransport.allocate_extends,
    `YulangClosure.NativeFreshScopeTransport.fresh_extends,
    `YulangClosure.NativeFreshScopeTransport.fresh_injective_on_old,
    `YulangClosure.NativeFreshScopeTransport.fresh_touched_range,
    `YulangClosure.NativeFreshScopeTransport.fresh_copied_disjoint_from_fixed,
    `YulangClosure.NativeFreshScopeTransport.fresh_evaluate,
    `YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse,
    `YulangClosure.NativeFreshScopeTransport.native_map_not_globally_injective,
    `YulangClosure.NativeFreshScopeTransport.repeated_key_overwrites_without_old_collision,
    `YulangClosure.NativeFreshScopeTransport.external_protection_survives_local_release
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
