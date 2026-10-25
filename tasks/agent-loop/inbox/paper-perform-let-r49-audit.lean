import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.PaperPerformLetExecution
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.universes true
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.resolveOperation_iff"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_eq"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.performStep_arity_mismatch"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.perform_applicable"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.perform_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_zero"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_outer"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.insertResponse_typed"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_applicable"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_extends"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_evidence"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.preservation"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.preservation
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.plug_step"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.evidence_erasure"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.erasure with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.erasure is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.erasure"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.erasure
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.erasure
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.erasure
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.erasure"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.trace_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.perform_empty_owner"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.requestBind_shape"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_nil"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.controlStep_request_cons"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_empty_owner"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.perform_requestTrace_empty_owner"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.requestTrace_trans"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.propagate_stack"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.perform_controlTrace_empty_owner"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.nonempty_owner_rejected"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.external_request with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.external_request is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.external_request"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.external_request
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.external_request
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.external_request
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.external_request"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.two_frames_order"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.repeated_declarations_resolve"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.conflicting_declarations_rejected"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.one_instance_fields"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.distinct_result_types"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.insertion_discriminator"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected"
#check @YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected
#print axioms YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperPerformLetExecution.unsupported_body_rejected"
