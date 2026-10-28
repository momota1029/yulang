import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalExtrusionWork
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
  let selected : Array Name := #[`YulangClosure.OriginalExtrusionWork]
  let required : Array Name := #[`YulangClosure.OriginalExtrusionWork.operation_local_memos,`YulangClosure.OriginalExtrusionWork.fresh_value_after_receiver,`YulangClosure.OriginalExtrusionWork.structural_work_first,`YulangClosure.OriginalExtrusionWork.pending_work_selected,`YulangClosure.OriginalExtrusionWork.rows_memo_first,`YulangClosure.OriginalExtrusionWork.memoized_visit,`YulangClosure.OriginalExtrusionWork.memo_insert_read,`YulangClosure.OriginalExtrusionWork.old_value_vector_selected,`YulangClosure.OriginalExtrusionWork.old_effect_vector_selected,`YulangClosure.OriginalExtrusionWork.allocate_value_ordinal,`YulangClosure.OriginalExtrusionWork.allocate_effect_ordinal,`YulangClosure.OriginalExtrusionWork.retain_does_not_merge,`YulangClosure.OriginalExtrusionWork.prepared_row_memo,`YulangClosure.OriginalExtrusionWork.memo_precedes_link_call,`YulangClosure.OriginalExtrusionWork.push_all_funded,`YulangClosure.OriginalExtrusionWork.selected_bound_job,`YulangClosure.OriginalExtrusionWork.selected_visit_job,`YulangClosure.OriginalExtrusionWork.bound_job_preserves_raw,`YulangClosure.OriginalExtrusionWork.schedule_bounds_computed,`YulangClosure.OriginalExtrusionWork.scheduled_old_bound,`YulangClosure.OriginalExtrusionWork.function_keys_computed,`YulangClosure.OriginalExtrusionWork.function_keys_have_four,`YulangClosure.OriginalExtrusionWork.bound_missing_stops,`YulangClosure.OriginalExtrusionWork.cell_constructor_readback,`YulangClosure.OriginalExtrusionWork.cell_constructor_immutable,`YulangClosure.OriginalExtrusionWork.selected_bound_dispatch,`YulangClosure.OriginalExtrusionWork.bound_dispatch_from_pending,`YulangClosure.OriginalExtrusionWork.bound_request_whole,`YulangClosure.OriginalExtrusionWork.function_visit_computed,`YulangClosure.OriginalExtrusionWork.copied_row_schedules,`YulangClosure.OriginalExtrusionWork.high_row_visit_schedules,`YulangClosure.OriginalExtrusionWork.Computed.argument_cell_computed,`YulangClosure.OriginalExtrusionWork.Computed.argument_effect_cell_computed,`YulangClosure.OriginalExtrusionWork.Computed.result_effect_cell_computed,`YulangClosure.OriginalExtrusionWork.Computed.result_cell_computed,`YulangClosure.OriginalExtrusionWork.Computed.row_terms_computed,`YulangClosure.OriginalExtrusionWork.Computed.function_keys_from_cells,`YulangClosure.OriginalExtrusionWork.Computed.function_rebuilt,`YulangClosure.OriginalExtrusionWork.Computed.post_publication_failure_retains_cells,`YulangClosure.OriginalExtrusionWork.Computed.negative_copy_in_function,`YulangClosure.OriginalExtrusionWork.Computed.row_bound_produced]
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
        logInfo m!"WORK_REVIEW_JSON {record.compress}"
    logInfo m!"WORK_REVIEW_CENSUS {moduleName} {count} {theorems}"
  for root in required do
    unless checked.contains root do throwError "missing theorem: {root}"
  logInfo m!"WORK_REVIEW_REQUIRED {required.size}"


#check @YulangClosure.OriginalExtrusionWork.operation_local_memos
#print axioms YulangClosure.OriginalExtrusionWork.operation_local_memos

#check @YulangClosure.OriginalExtrusionWork.fresh_value_after_receiver
#print axioms YulangClosure.OriginalExtrusionWork.fresh_value_after_receiver

#check @YulangClosure.OriginalExtrusionWork.structural_work_first
#print axioms YulangClosure.OriginalExtrusionWork.structural_work_first

#check @YulangClosure.OriginalExtrusionWork.pending_work_selected
#print axioms YulangClosure.OriginalExtrusionWork.pending_work_selected

#check @YulangClosure.OriginalExtrusionWork.rows_memo_first
#print axioms YulangClosure.OriginalExtrusionWork.rows_memo_first

#check @YulangClosure.OriginalExtrusionWork.memoized_visit
#print axioms YulangClosure.OriginalExtrusionWork.memoized_visit

#check @YulangClosure.OriginalExtrusionWork.memo_insert_read
#print axioms YulangClosure.OriginalExtrusionWork.memo_insert_read

#check @YulangClosure.OriginalExtrusionWork.old_value_vector_selected
#print axioms YulangClosure.OriginalExtrusionWork.old_value_vector_selected

#check @YulangClosure.OriginalExtrusionWork.old_effect_vector_selected
#print axioms YulangClosure.OriginalExtrusionWork.old_effect_vector_selected

#check @YulangClosure.OriginalExtrusionWork.allocate_value_ordinal
#print axioms YulangClosure.OriginalExtrusionWork.allocate_value_ordinal

#check @YulangClosure.OriginalExtrusionWork.allocate_effect_ordinal
#print axioms YulangClosure.OriginalExtrusionWork.allocate_effect_ordinal

#check @YulangClosure.OriginalExtrusionWork.retain_does_not_merge
#print axioms YulangClosure.OriginalExtrusionWork.retain_does_not_merge

#check @YulangClosure.OriginalExtrusionWork.prepared_row_memo
#print axioms YulangClosure.OriginalExtrusionWork.prepared_row_memo

#check @YulangClosure.OriginalExtrusionWork.memo_precedes_link_call
#print axioms YulangClosure.OriginalExtrusionWork.memo_precedes_link_call

#check @YulangClosure.OriginalExtrusionWork.push_all_funded
#print axioms YulangClosure.OriginalExtrusionWork.push_all_funded

#check @YulangClosure.OriginalExtrusionWork.selected_bound_job
#print axioms YulangClosure.OriginalExtrusionWork.selected_bound_job

#check @YulangClosure.OriginalExtrusionWork.selected_visit_job
#print axioms YulangClosure.OriginalExtrusionWork.selected_visit_job

#check @YulangClosure.OriginalExtrusionWork.bound_job_preserves_raw
#print axioms YulangClosure.OriginalExtrusionWork.bound_job_preserves_raw

#check @YulangClosure.OriginalExtrusionWork.schedule_bounds_computed
#print axioms YulangClosure.OriginalExtrusionWork.schedule_bounds_computed

#check @YulangClosure.OriginalExtrusionWork.scheduled_old_bound
#print axioms YulangClosure.OriginalExtrusionWork.scheduled_old_bound

#check @YulangClosure.OriginalExtrusionWork.function_keys_computed
#print axioms YulangClosure.OriginalExtrusionWork.function_keys_computed

#check @YulangClosure.OriginalExtrusionWork.function_keys_have_four
#print axioms YulangClosure.OriginalExtrusionWork.function_keys_have_four

#check @YulangClosure.OriginalExtrusionWork.bound_missing_stops
#print axioms YulangClosure.OriginalExtrusionWork.bound_missing_stops

#check @YulangClosure.OriginalExtrusionWork.cell_constructor_readback
#print axioms YulangClosure.OriginalExtrusionWork.cell_constructor_readback

#check @YulangClosure.OriginalExtrusionWork.cell_constructor_immutable
#print axioms YulangClosure.OriginalExtrusionWork.cell_constructor_immutable

#check @YulangClosure.OriginalExtrusionWork.selected_bound_dispatch
#print axioms YulangClosure.OriginalExtrusionWork.selected_bound_dispatch

#check @YulangClosure.OriginalExtrusionWork.bound_dispatch_from_pending
#print axioms YulangClosure.OriginalExtrusionWork.bound_dispatch_from_pending

#check @YulangClosure.OriginalExtrusionWork.bound_request_whole
#print axioms YulangClosure.OriginalExtrusionWork.bound_request_whole

#check @YulangClosure.OriginalExtrusionWork.function_visit_computed
#print axioms YulangClosure.OriginalExtrusionWork.function_visit_computed

#check @YulangClosure.OriginalExtrusionWork.copied_row_schedules
#print axioms YulangClosure.OriginalExtrusionWork.copied_row_schedules

#check @YulangClosure.OriginalExtrusionWork.high_row_visit_schedules
#print axioms YulangClosure.OriginalExtrusionWork.high_row_visit_schedules

#check @YulangClosure.OriginalExtrusionWork.Computed.argument_cell_computed
#print axioms YulangClosure.OriginalExtrusionWork.Computed.argument_cell_computed

#check @YulangClosure.OriginalExtrusionWork.Computed.argument_effect_cell_computed
#print axioms YulangClosure.OriginalExtrusionWork.Computed.argument_effect_cell_computed

#check @YulangClosure.OriginalExtrusionWork.Computed.result_effect_cell_computed
#print axioms YulangClosure.OriginalExtrusionWork.Computed.result_effect_cell_computed

#check @YulangClosure.OriginalExtrusionWork.Computed.result_cell_computed
#print axioms YulangClosure.OriginalExtrusionWork.Computed.result_cell_computed

#check @YulangClosure.OriginalExtrusionWork.Computed.row_terms_computed
#print axioms YulangClosure.OriginalExtrusionWork.Computed.row_terms_computed

#check @YulangClosure.OriginalExtrusionWork.Computed.function_keys_from_cells
#print axioms YulangClosure.OriginalExtrusionWork.Computed.function_keys_from_cells

#check @YulangClosure.OriginalExtrusionWork.Computed.function_rebuilt
#print axioms YulangClosure.OriginalExtrusionWork.Computed.function_rebuilt

#check @YulangClosure.OriginalExtrusionWork.Computed.post_publication_failure_retains_cells
#print axioms YulangClosure.OriginalExtrusionWork.Computed.post_publication_failure_retains_cells

#check @YulangClosure.OriginalExtrusionWork.Computed.negative_copy_in_function
#print axioms YulangClosure.OriginalExtrusionWork.Computed.negative_copy_in_function

#check @YulangClosure.OriginalExtrusionWork.Computed.row_bound_produced
#print axioms YulangClosure.OriginalExtrusionWork.Computed.row_bound_produced
