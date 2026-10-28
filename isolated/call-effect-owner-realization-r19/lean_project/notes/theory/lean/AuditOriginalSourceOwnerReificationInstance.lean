import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalSourceOwnerReificationInstance
set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.site_rows with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.site_rows is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.site_rows"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.site_rows
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.site_rows
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.site_rows
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.site_rows"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.name_rows with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.name_rows is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.name_rows"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.name_rows
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.name_rows
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.name_rows
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.name_rows"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.argument_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.argument_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.argument_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.argument_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.argument_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.argument_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.argument_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.inner_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.inner_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.inner_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.inner_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.inner_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.inner_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.inner_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.body_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.body_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.body_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.body_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.body_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.body_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.body_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source"
#check @YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source
#print axioms YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source"
