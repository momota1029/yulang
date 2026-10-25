import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.PaperPerformLetExecution
open Lean Elab Command
run_cmd do
  let roots : Array Name := #[`YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.preservation,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.erasure,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.external_request,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator,
    `YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected]
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut index := 0
  while index < pending.size do
    if index > 500 then throwError "dependency diagnostic exceeded 500 nodes"
    let name := pending[index]!
    index := index + 1
    if !seen.contains name then
      seen := seen.insert name
      let axioms ← Lean.collectAxioms name
      if axioms.contains `Classical.choice then
        let env ← getEnv
        if let some info := env.find? name then
          let deps := info.type.getUsedConstants ++
            ((info.value? true).map Lean.Expr.getUsedConstants).getD #[]
          logInfo m!"CHOICE_NODE {name}"
          for dep in deps do
            let depAxioms ← Lean.collectAxioms dep
            if depAxioms.contains `Classical.choice then
              logInfo m!"CHOICE_EDGE {name} -> {dep}"
              pending := pending.push dep
        else logInfo m!"CHOICE_UNAVAILABLE {name}"
  logInfo m!"DIAGNOSTIC_VISITED {seen.toArray.size}"
