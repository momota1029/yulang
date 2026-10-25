import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.PaperTupleSplitExecution
set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_tail with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_tail is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_tail"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_tail
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_tail
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_tail
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_tail"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.values_length with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.values_length is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.values_length"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.values_length
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.values_length
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.values_length
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.values_length"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_typed with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_typed is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_typed"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_typed
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_typed
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_typed
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_typed"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_identity_typed with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_identity_typed is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_identity_typed"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_identity_typed
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_identity_typed
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_identity_typed
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.tupleReplacement_identity_typed"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_eq with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_eq is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_eq"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_eq
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_eq
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_eq
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_eq"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_arity_mismatch with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_arity_mismatch is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_arity_mismatch"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_arity_mismatch
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_arity_mismatch
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_arity_mismatch
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_arity_mismatch"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable_of_components with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable_of_components is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable_of_components"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable_of_components
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable_of_components
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable_of_components
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable_of_components"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.split_applicable"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.split_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.split_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.split_preservation"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.split_preservation
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.split_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.split_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.split_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.step_extends with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.step_extends is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.step_extends"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.step_extends
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.step_extends
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.step_extends
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.step_extends"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_to_step with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_to_step is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_to_step"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_to_step
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_to_step
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_to_step
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.splitStep_to_step"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.preservation"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.preservation
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_extends with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_extends is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_extends"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_extends
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_extends
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_extends
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_extends"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_evidence with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_evidence is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_evidence"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_evidence
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_evidence
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_evidence
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.controlStep_evidence"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_preservation"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_preservation
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.control_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.control_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.control_preservation"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.control_preservation
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.control_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.control_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.control_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.old_context_step with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.old_context_step is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.old_context_step"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.old_context_step
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.old_context_step
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.old_context_step
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.old_context_step"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.plug_step with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.plug_step is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.plug_step"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.plug_step
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.plug_step
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.plug_step
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.plug_step"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_erasure with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_erasure is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_erasure"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_erasure
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_erasure
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_erasure
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.evidence_erasure"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.erasure with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.erasure is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.erasure"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.erasure
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.erasure
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.erasure
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.erasure"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.trace_preservation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.trace_preservation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.trace_preservation"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.trace_preservation
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.trace_preservation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.trace_preservation
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.trace_preservation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_order with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.example_order is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.example_order"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.example_order
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.example_order
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_order
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.example_order"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_empty with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.example_empty is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.example_empty"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.example_empty
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.example_empty
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_empty
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.example_empty"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_external_under_binder with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.example_external_under_binder is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.example_external_under_binder"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.example_external_under_binder
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.example_external_under_binder
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_external_under_binder
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.example_external_under_binder"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_arity_mismatch with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.example_arity_mismatch is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.example_arity_mismatch"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.example_arity_mismatch
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.example_arity_mismatch
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_arity_mismatch
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.example_arity_mismatch"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_not_sequential with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperTupleSplitExecution.example_not_sequential is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTupleSplitExecution.example_not_sequential"
#check @YulangClosure.PaperTypes.PaperTupleSplitExecution.example_not_sequential
#print axioms YulangClosure.PaperTypes.PaperTupleSplitExecution.example_not_sequential
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperTupleSplitExecution.example_not_sequential
  for ax in axioms do
    unless #[`propext, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTupleSplitExecution.example_not_sequential"
