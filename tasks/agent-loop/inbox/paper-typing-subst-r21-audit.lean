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
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment"
#check @YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment
#print axioms YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperComputationTyped.splitInversion with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperComputationTyped.splitInversion is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.splitInversion"
#check @YulangClosure.PaperTypes.PaperComputationTyped.splitInversion
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.splitInversion
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperComputationTyped.splitInversion
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.splitInversion"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PaperTypes.PaperComputationTyped.splitTuple with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.PaperTypes.PaperComputationTyped.splitTuple is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.splitTuple"
#check @YulangClosure.PaperTypes.PaperComputationTyped.splitTuple
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.splitTuple
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.PaperTypes.PaperComputationTyped.splitTuple
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.splitTuple"

#check @YulangClosure.PaperTypes.PaperComputationTyped.split
#print axioms YulangClosure.PaperTypes.PaperComputationTyped.split
#print YulangClosure.PaperTypes.extendTupleEnvironment
