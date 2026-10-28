import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.NativeInferenceProgress
set_option pp.fullNames true
set_option pp.universes false
open Lean Elab Command
run_cmd do
  let moduleName := `YulangClosure.NativeInferenceProgress
  let roots : Array Name := #[
    `YulangClosure.NativeInferenceProgress.source_context_atom,
    `YulangClosure.NativeInferenceProgress.admitted_context_atom,
    `YulangClosure.NativeInferenceProgress.filter_bound_identity,
    `YulangClosure.NativeInferenceProgress.decompose_fibers_identity,
    `YulangClosure.NativeInferenceProgress.decompose_children_atom,
    `YulangClosure.NativeInferenceProgress.value_port_context_atom,
    `YulangClosure.NativeInferenceProgress.total_next,
    `YulangClosure.NativeInferenceProgress.total_reject,
    `YulangClosure.NativeInferenceProgress.total_finish,
    `YulangClosure.NativeInferenceProgress.total_bind,
    `YulangClosure.NativeInferenceProgress.atomic_scan_clean,
    `YulangClosure.NativeInferenceProgress.replay_scan_clean,
    `YulangClosure.NativeInferenceProgress.shallow_scan_clean,
    `YulangClosure.NativeInferenceProgress.consume_context_closure,
    `YulangClosure.NativeInferenceProgress.expand_consumes,
    `YulangClosure.NativeInferenceProgress.native_expand_context_closure,
    `YulangClosure.NativeInferenceProgress.signature_fiber_atom,
    `YulangClosure.NativeInferenceProgress.post_atom,
    `YulangClosure.NativeInferenceProgress.transport_atom,
    `YulangClosure.NativeInferenceProgress.replay_context_shallow,
    `YulangClosure.NativeInferenceProgress.renamed_atom,
    `YulangClosure.NativeInferenceProgress.step_invariant,
    `YulangClosure.NativeInferenceProgress.reachable_context_closure,
    `YulangClosure.NativeInferenceProgress.atom_extension,
    `YulangClosure.NativeInferenceProgress.shallow_extension,
    `YulangClosure.NativeInferenceProgress.invariant_extension,
    `YulangClosure.NativeInferenceProgress.growing_context_closure,
    `YulangClosure.NativeInferenceProgress.fresh_prefix_constructed
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
      logInfo m!"NATIVE_PROGRESS_AUDIT_BEGIN {kind} {name}"
      let id := mkIdent name
      elabCommand (← `(#check @$id))
      elabCommand (← `(#print axioms $id))
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "unapproved axiom in {name}: {ax}"
      logInfo m!"NATIVE_PROGRESS_AUDIT_END {name}"
  for root in roots do
    unless theorems.contains root do
      throwError "missing originating theorem: {root}"
  logInfo m!"NATIVE_PROGRESS_AUDIT_TOTAL declarations={total} theorems={theorems.size} required={roots.size}"
