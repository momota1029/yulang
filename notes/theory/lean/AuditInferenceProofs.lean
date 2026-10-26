import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.InferenceProofs

/-! Exact originating-module audit, including private and generated theorems.
Run `lake build` followed by `lake env lean -j1 -M1024 AuditInferenceProofs.lean`.
Kernel acceptance does not establish unprovided theorem premises or source meaning.
-/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false

open Lean Elab Command

run_cmd do
  let modules : Array Name := #[`YulangClosure.BirthLevelSCC]
  let roots : Array Name := #[
    `YulangClosure.BirthLevelSCC.finiteReach_iff,
    `YulangClosure.BirthLevelSCC.projection_filter_iff,
    `YulangClosure.BirthLevelSCC.filtered_compression_iff,
    `YulangClosure.BirthLevelSCC.finite_helper_qualifies_iff
  ]
  let env ← getEnv
  let mut targets : Array Name := #[]
  for moduleName in modules do
    let some moduleIndex := env.getModuleIdx? moduleName
      | throwError "audited module is not imported: {moduleName}"
    let mut count : Nat := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some moduleIndex then
        match info with
        | .thmInfo _ =>
            if targets.contains name then
              throwError "duplicate theorem: {name}"
            targets := targets.push name
            count := count + 1
        | .axiomInfo _ => throwError "project axiom: {name}"
        | _ => pure ()
    if count == 0 then
      throwError "empty theorem inventory: {moduleName}"
    logInfo m!"YULANG_AUDIT_MODULE {moduleName} {count}"
  for root in roots do
    unless targets.contains root do
      throwError "missing required theorem: {root}"
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
