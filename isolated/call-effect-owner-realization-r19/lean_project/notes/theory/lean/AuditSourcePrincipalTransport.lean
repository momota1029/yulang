import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.SourcePrincipalTransport
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
open Lean Elab Command
run_cmd do
  let moduleName := `YulangClosure.SourcePrincipalTransport
  let roots : Array Name := #[
    `YulangClosure.SourcePrincipalTransport.program_call_owners,
    `YulangClosure.SourcePrincipalTransport.actual_body_bindings,
    `YulangClosure.SourcePrincipalTransport.recursive_name_is_monomorphic,
    `YulangClosure.SourcePrincipalTransport.h_call_complete_rule,
    `YulangClosure.SourcePrincipalTransport.recursive_call_complete_rule,
    `YulangClosure.SourcePrincipalTransport.recursive_field_retains_h_suffix,
    `YulangClosure.SourcePrincipalTransport.h_name_source_derivation,
    `YulangClosure.SourcePrincipalTransport.source_owners_after_all_frames,
    `YulangClosure.SourcePrincipalTransport.source_subjects_after_all_frames,
    `YulangClosure.SourcePrincipalTransport.h_return_supplies_current_receiver
  ]
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "module missing: {moduleName}"
  let mut theorems : Array Name := #[]
  let mut total : Nat := 0
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then
      let kind : String ← match info with
        | .thmInfo _ =>
            theorems := theorems.push name
            pure "theorem"
        | .axiomInfo _ => throwError "project axiom: {name}"
        | .defnInfo _ => pure "definition"
        | .opaqueInfo _ => pure "opaque"
        | .inductInfo _ => pure "inductive"
        | .ctorInfo _ => pure "constructor"
        | .recInfo _ => pure "recursor"
        | .quotInfo _ => pure "quotient"
      total := total + 1
      logInfo m!"SOURCE_PRINCIPAL_AUDIT_BEGIN {kind} {name}"
      let id := mkIdent name
      elabCommand (← `(#check @$id))
      elabCommand (← `(#print axioms $id))
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "unapproved axiom in {name}: {ax}"
      logInfo m!"SOURCE_PRINCIPAL_AUDIT_END {name}"
  for root in roots do
    unless theorems.contains root do
      throwError "missing originating theorem: {root}"
  logInfo m!"SOURCE_PRINCIPAL_AUDIT_TOTAL declarations={total} theorems={theorems.size} required={roots.size}"
