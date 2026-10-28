import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalExtrusionFibers
import YulangClosure.OriginalFiberTransfer
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[`YulangClosure.OriginalExtrusionFibers,`YulangClosure.OriginalFiberTransfer]
  let required : Array Name := #[`YulangClosure.OriginalExtrusionFibers.remap_flow_metadata,`YulangClosure.OriginalExtrusionFibers.transport_key_exact,`YulangClosure.OriginalExtrusionFibers.transfer_valid,`YulangClosure.OriginalExtrusionFibers.transferred_fiber_exact,`YulangClosure.OriginalExtrusionFibers.transfer_captured_source,`YulangClosure.OriginalExtrusionFibers.transfer_native_run,`YulangClosure.OriginalExtrusionFibers.transfer_fiber_run,`YulangClosure.OriginalExtrusionFibers.transfer_history,`YulangClosure.OriginalExtrusionFibers.transfer_old_readback,`YulangClosure.OriginalExtrusionFibers.transfer_preserves_fiber,`YulangClosure.OriginalFiberTransfer.prepare_snapshot,`YulangClosure.OriginalFiberTransfer.completed_exact,`YulangClosure.OriginalFiberTransfer.fiber_run_trans,`YulangClosure.OriginalFiberTransfer.native_run_trans,`YulangClosure.OriginalFiberTransfer.loop_footprints,`YulangClosure.OriginalFiberTransfer.loop_old_readback,`YulangClosure.OriginalFiberTransfer.loop_preserves_fiber,`YulangClosure.OriginalFiberTransfer.loop_captured_cursor,`YulangClosure.OriginalFiberTransfer.loop_complete_entries,`YulangClosure.OriginalFiberTransfer.loop_call_facts,`YulangClosure.OriginalFiberTransfer.call_delivered,`YulangClosure.OriginalFiberTransfer.loop_delivers,`YulangClosure.OriginalFiberTransfer.bound_complete,`YulangClosure.OriginalFiberTransfer.loop_addressed,`YulangClosure.OriginalFiberTransfer.bound_cursor_formed]
  let mut checked : Array Name := #[]
  for moduleName in selected do
    let some idx := env.getModuleIdx? moduleName | throwError "missing module: {moduleName}"
    let mut count : Nat := 0
    let mut theorems : Nat := 0
    for (name,info) in env.constants.toList do
      if env.getModuleIdxFor? name == some idx then
        count := count + 1
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        if kind == "axiom" then throwError "new axiom: {name}"
        if kind == "theorem" then
          theorems := theorems + 1
          checked := checked.push name
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
            throwError "unapproved axiom: {name}: {ax}"
        let type ← liftTermElabM (Lean.Meta.ppExpr info.type)
        let record := Json.mkObj [
          ("module",Json.str (toString moduleName)),("name",Json.str (toString name)),
          ("kind",Json.str kind),("type",Json.str type.pretty),
          ("axioms",Json.arr (axioms.map (fun ax => Json.str (toString ax))))]
        logInfo m!"FIBER_REVIEW_JSON {record.compress}"
    logInfo m!"FIBER_REVIEW_CENSUS {moduleName} {count} {theorems}"
  for root in required do
    unless checked.contains root do throwError "missing theorem: {root}"
  logInfo m!"FIBER_REVIEW_REQUIRED {required.size}"

#check @YulangClosure.OriginalExtrusionFibers.remap_flow_metadata
#print axioms YulangClosure.OriginalExtrusionFibers.remap_flow_metadata

#check @YulangClosure.OriginalExtrusionFibers.transport_key_exact
#print axioms YulangClosure.OriginalExtrusionFibers.transport_key_exact

#check @YulangClosure.OriginalExtrusionFibers.transfer_valid
#print axioms YulangClosure.OriginalExtrusionFibers.transfer_valid

#check @YulangClosure.OriginalExtrusionFibers.transferred_fiber_exact
#print axioms YulangClosure.OriginalExtrusionFibers.transferred_fiber_exact

#check @YulangClosure.OriginalExtrusionFibers.transfer_captured_source
#print axioms YulangClosure.OriginalExtrusionFibers.transfer_captured_source

#check @YulangClosure.OriginalExtrusionFibers.transfer_native_run
#print axioms YulangClosure.OriginalExtrusionFibers.transfer_native_run

#check @YulangClosure.OriginalExtrusionFibers.transfer_fiber_run
#print axioms YulangClosure.OriginalExtrusionFibers.transfer_fiber_run

#check @YulangClosure.OriginalExtrusionFibers.transfer_history
#print axioms YulangClosure.OriginalExtrusionFibers.transfer_history

#check @YulangClosure.OriginalExtrusionFibers.transfer_old_readback
#print axioms YulangClosure.OriginalExtrusionFibers.transfer_old_readback

#check @YulangClosure.OriginalExtrusionFibers.transfer_preserves_fiber
#print axioms YulangClosure.OriginalExtrusionFibers.transfer_preserves_fiber

#check @YulangClosure.OriginalFiberTransfer.prepare_snapshot
#print axioms YulangClosure.OriginalFiberTransfer.prepare_snapshot

#check @YulangClosure.OriginalFiberTransfer.completed_exact
#print axioms YulangClosure.OriginalFiberTransfer.completed_exact

#check @YulangClosure.OriginalFiberTransfer.fiber_run_trans
#print axioms YulangClosure.OriginalFiberTransfer.fiber_run_trans

#check @YulangClosure.OriginalFiberTransfer.native_run_trans
#print axioms YulangClosure.OriginalFiberTransfer.native_run_trans

#check @YulangClosure.OriginalFiberTransfer.loop_footprints
#print axioms YulangClosure.OriginalFiberTransfer.loop_footprints

#check @YulangClosure.OriginalFiberTransfer.loop_old_readback
#print axioms YulangClosure.OriginalFiberTransfer.loop_old_readback

#check @YulangClosure.OriginalFiberTransfer.loop_preserves_fiber
#print axioms YulangClosure.OriginalFiberTransfer.loop_preserves_fiber

#check @YulangClosure.OriginalFiberTransfer.loop_captured_cursor
#print axioms YulangClosure.OriginalFiberTransfer.loop_captured_cursor

#check @YulangClosure.OriginalFiberTransfer.loop_complete_entries
#print axioms YulangClosure.OriginalFiberTransfer.loop_complete_entries

#check @YulangClosure.OriginalFiberTransfer.loop_call_facts
#print axioms YulangClosure.OriginalFiberTransfer.loop_call_facts

#check @YulangClosure.OriginalFiberTransfer.call_delivered
#print axioms YulangClosure.OriginalFiberTransfer.call_delivered

#check @YulangClosure.OriginalFiberTransfer.loop_delivers
#print axioms YulangClosure.OriginalFiberTransfer.loop_delivers

#check @YulangClosure.OriginalFiberTransfer.bound_complete
#print axioms YulangClosure.OriginalFiberTransfer.bound_complete

#check @YulangClosure.OriginalFiberTransfer.loop_addressed
#print axioms YulangClosure.OriginalFiberTransfer.loop_addressed

#check @YulangClosure.OriginalFiberTransfer.bound_cursor_formed
#print axioms YulangClosure.OriginalFiberTransfer.bound_cursor_formed
