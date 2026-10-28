/- Reusable declaration-kind, complete type and transitive axiom audit.
These are conditional source-owner constructions, not caller/native closure. -/
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalSourceOwnerReification
set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.coordinate_laws_of_rows with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.coordinate_laws_of_rows is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.coordinate_laws_of_rows"
#check @YulangClosure.OriginalSourceOwnerReification.coordinate_laws_of_rows
#print axioms YulangClosure.OriginalSourceOwnerReification.coordinate_laws_of_rows
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.coordinate_laws_of_rows
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.coordinate_laws_of_rows"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.table_to_source_erasure with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.table_to_source_erasure is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.table_to_source_erasure"
#check @YulangClosure.OriginalSourceOwnerReification.table_to_source_erasure
#print axioms YulangClosure.OriginalSourceOwnerReification.table_to_source_erasure
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.table_to_source_erasure
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.table_to_source_erasure"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.inner_owner_available with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.inner_owner_available is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.inner_owner_available"
#check @YulangClosure.OriginalSourceOwnerReification.inner_owner_available
#print axioms YulangClosure.OriginalSourceOwnerReification.inner_owner_available
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.inner_owner_available
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.inner_owner_available"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.local_ambient_kinds with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.local_ambient_kinds is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.local_ambient_kinds"
#check @YulangClosure.OriginalSourceOwnerReification.local_ambient_kinds
#print axioms YulangClosure.OriginalSourceOwnerReification.local_ambient_kinds
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.local_ambient_kinds
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.local_ambient_kinds"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.target_invocation_binder with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.target_invocation_binder is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.target_invocation_binder"
#check @YulangClosure.OriginalSourceOwnerReification.target_invocation_binder
#print axioms YulangClosure.OriginalSourceOwnerReification.target_invocation_binder
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.target_invocation_binder
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.target_invocation_binder"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.identity_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.identity_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.identity_source"
#check @YulangClosure.OriginalSourceOwnerReification.identity_source
#print axioms YulangClosure.OriginalSourceOwnerReification.identity_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.identity_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.identity_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.identity_registration with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.identity_registration is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.identity_registration"
#check @YulangClosure.OriginalSourceOwnerReification.identity_registration
#print axioms YulangClosure.OriginalSourceOwnerReification.identity_registration
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.identity_registration
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.identity_registration"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.identity_body_binding with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.identity_body_binding is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.identity_body_binding"
#check @YulangClosure.OriginalSourceOwnerReification.identity_body_binding
#print axioms YulangClosure.OriginalSourceOwnerReification.identity_body_binding
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.identity_body_binding
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.identity_body_binding"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.application_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.application_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.application_source"
#check @YulangClosure.OriginalSourceOwnerReification.application_source
#print axioms YulangClosure.OriginalSourceOwnerReification.application_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.application_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.application_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.application_owners with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.application_owners is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.application_owners"
#check @YulangClosure.OriginalSourceOwnerReification.application_owners
#print axioms YulangClosure.OriginalSourceOwnerReification.application_owners
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.application_owners
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.application_owners"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.identity_invocation_owner with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.identity_invocation_owner is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.identity_invocation_owner"
#check @YulangClosure.OriginalSourceOwnerReification.identity_invocation_owner
#print axioms YulangClosure.OriginalSourceOwnerReification.identity_invocation_owner
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.identity_invocation_owner
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.identity_invocation_owner"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.target_scope_from_root with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.target_scope_from_root is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.target_scope_from_root"
#check @YulangClosure.OriginalSourceOwnerReification.target_scope_from_root
#print axioms YulangClosure.OriginalSourceOwnerReification.target_scope_from_root
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.target_scope_from_root
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.target_scope_from_root"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReification.introduction_scope_binders with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReification.introduction_scope_binders is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReification.introduction_scope_binders"
#check @YulangClosure.OriginalSourceOwnerReification.introduction_scope_binders
#print axioms YulangClosure.OriginalSourceOwnerReification.introduction_scope_binders
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReification.introduction_scope_binders
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReification.introduction_scope_binders"
