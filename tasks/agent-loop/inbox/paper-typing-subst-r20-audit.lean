import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.PaperExecutionTypingSubstitution
set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperValueTyped.subst_explicit with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperValueTyped.subst_explicit is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperValueTyped.subst_explicit"
#check @YulangClosure.PaperTypes.PaperValueTyped.subst_explicit
#print axioms YulangClosure.PaperTypes.PaperValueTyped.subst_explicit
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperValueTyped.subst_explicit
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperValueTyped.subst_explicit"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.ValuesTyped.typeTransport with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.ValuesTyped.typeTransport is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.ValuesTyped.typeTransport"
#check @YulangClosure.PaperTypes.ValuesTyped.typeTransport
#print axioms YulangClosure.PaperTypes.ValuesTyped.typeTransport
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.ValuesTyped.typeTransport
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.ValuesTyped.typeTransport"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.ValuesAllTyped.typeTransport with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.ValuesAllTyped.typeTransport is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.ValuesAllTyped.typeTransport"
#check @YulangClosure.PaperTypes.ValuesAllTyped.typeTransport
#print axioms YulangClosure.PaperTypes.ValuesAllTyped.typeTransport
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.ValuesAllTyped.typeTransport
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.ValuesAllTyped.typeTransport"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport"
#check @YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport
#print axioms YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperComputationTyped.typeTransport with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperComputationTyped.typeTransport is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.typeTransport"
#check @YulangClosure.PaperTypes.PaperComputationTyped.typeTransport
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.typeTransport
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperComputationTyped.typeTransport
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.typeTransport"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport"
#check @YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport
#print axioms YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion"
#check @YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft"
#check @YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight"
#check @YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight"

#check @YulangClosure.PaperTypes.PaperComputationTyped.unionCase
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.unionCase
