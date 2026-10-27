import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalProviderSourceSolution
set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.body_resolves_original_formal with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.body_resolves_original_formal is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.body_resolves_original_formal"
#check @YulangClosure.OriginalProviderSourceSolution.body_resolves_original_formal
#print axioms YulangClosure.OriginalProviderSourceSolution.body_resolves_original_formal
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.body_resolves_original_formal
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.body_resolves_original_formal"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.provider_source_rules with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.provider_source_rules is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.provider_source_rules"
#check @YulangClosure.OriginalProviderSourceSolution.provider_source_rules
#print axioms YulangClosure.OriginalProviderSourceSolution.provider_source_rules
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.provider_source_rules
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.provider_source_rules"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_initializer with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_initializer is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_initializer"
#check @YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_initializer
#print axioms YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_initializer
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_initializer
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_initializer"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.completed_cut_retains_scope with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.completed_cut_retains_scope is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.completed_cut_retains_scope"
#check @YulangClosure.OriginalProviderSourceSolution.completed_cut_retains_scope
#print axioms YulangClosure.OriginalProviderSourceSolution.completed_cut_retains_scope
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.completed_cut_retains_scope
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.completed_cut_retains_scope"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.completed_cut_candidate with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.completed_cut_candidate is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.completed_cut_candidate"
#check @YulangClosure.OriginalProviderSourceSolution.completed_cut_candidate
#print axioms YulangClosure.OriginalProviderSourceSolution.completed_cut_candidate
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.completed_cut_candidate
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.completed_cut_candidate"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_fixed_record with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_fixed_record is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_fixed_record"
#check @YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_fixed_record
#print axioms YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_fixed_record
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_fixed_record
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.provider_solution_requires_fixed_record"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.provider_fixed_record_is_unique with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.provider_fixed_record_is_unique is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.provider_fixed_record_is_unique"
#check @YulangClosure.OriginalProviderSourceSolution.provider_fixed_record_is_unique
#print axioms YulangClosure.OriginalProviderSourceSolution.provider_fixed_record_is_unique
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.provider_fixed_record_is_unique
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.provider_fixed_record_is_unique"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.scoped_return_identity_injective with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.scoped_return_identity_injective is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.scoped_return_identity_injective"
#check @YulangClosure.OriginalProviderSourceSolution.scoped_return_identity_injective
#print axioms YulangClosure.OriginalProviderSourceSolution.scoped_return_identity_injective
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.scoped_return_identity_injective
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.scoped_return_identity_injective"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.scoped_candidates_agree with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.scoped_candidates_agree is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.scoped_candidates_agree"
#check @YulangClosure.OriginalProviderSourceSolution.scoped_candidates_agree
#print axioms YulangClosure.OriginalProviderSourceSolution.scoped_candidates_agree
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.scoped_candidates_agree
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.scoped_candidates_agree"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.finite_completion_preserves_prior with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.finite_completion_preserves_prior is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.finite_completion_preserves_prior"
#check @YulangClosure.OriginalProviderSourceSolution.finite_completion_preserves_prior
#print axioms YulangClosure.OriginalProviderSourceSolution.finite_completion_preserves_prior
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.finite_completion_preserves_prior
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.finite_completion_preserves_prior"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.finite_completion_contains_candidates with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.finite_completion_contains_candidates is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.finite_completion_contains_candidates"
#check @YulangClosure.OriginalProviderSourceSolution.finite_completion_contains_candidates
#print axioms YulangClosure.OriginalProviderSourceSolution.finite_completion_contains_candidates
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.finite_completion_contains_candidates
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.finite_completion_contains_candidates"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.finite_completion_candidate_valid with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.finite_completion_candidate_valid is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.finite_completion_candidate_valid"
#check @YulangClosure.OriginalProviderSourceSolution.finite_completion_candidate_valid
#print axioms YulangClosure.OriginalProviderSourceSolution.finite_completion_candidate_valid
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.finite_completion_candidate_valid
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.finite_completion_candidate_valid"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.original_admitted_finite_completion with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.original_admitted_finite_completion is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.original_admitted_finite_completion"
#check @YulangClosure.OriginalProviderSourceSolution.original_admitted_finite_completion
#print axioms YulangClosure.OriginalProviderSourceSolution.original_admitted_finite_completion
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.original_admitted_finite_completion
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.original_admitted_finite_completion"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.completion_preserves_original_readout with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.completion_preserves_original_readout is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.completion_preserves_original_readout"
#check @YulangClosure.OriginalProviderSourceSolution.completion_preserves_original_readout
#print axioms YulangClosure.OriginalProviderSourceSolution.completion_preserves_original_readout
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.completion_preserves_original_readout
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.completion_preserves_original_readout"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalProviderSourceSolution.complete_record_transport with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalProviderSourceSolution.complete_record_transport is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.complete_record_transport"
#check @YulangClosure.OriginalProviderSourceSolution.complete_record_transport
#print axioms YulangClosure.OriginalProviderSourceSolution.complete_record_transport
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalProviderSourceSolution.complete_record_transport
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.complete_record_transport"
