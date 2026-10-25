import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.PaperExtendedExecution
import YulangClosure.PaperEliminationExamples

/-!
Reproducible exact-name audit of the explicit-execution additions and their
changed typing, substitution, and core-execution foundations.
After `lake build`, run `lake env lean -j1 -M1024 AuditExecutionProofs.lean`.
This enumerates theorem constants by their actual originating module, including
private and compiler-generated helpers. It checks declarations and axioms;
source correspondence and all theorem hypotheses still require review.
-/

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false

open Lean Elab Command

run_cmd do
  let modules : Array Name := #[
    `YulangClosure.PaperExecutionSyntax,
    `YulangClosure.PaperExecutionTypingSubstitution,
    `YulangClosure.PaperExecutionGraphWeakening,
    `YulangClosure.PaperTermSubstitution,
    `YulangClosure.PaperCoreStep,
    `YulangClosure.PaperCoreControl,
    `YulangClosure.PaperTypeApplicationPreservation,
    `YulangClosure.PaperTemplateExecution,
    `YulangClosure.PaperCombinedExecution,
    `YulangClosure.PaperExtendedExecution,
    `YulangClosure.PaperEliminationExamples
  ]
  let roots : Array Name := #[
    `YulangClosure.PaperTypes.PaperValueTyped.subst_explicit,
    `YulangClosure.PaperTypes.PaperValueTyped.graphWeaken,
    `YulangClosure.PaperTypes.PaperValueTyped.termRename,
    `YulangClosure.PaperTypes.PaperValueTyped.termReplace,
    `YulangClosure.PaperTypes.PaperValueTyped.termSupported,
    `YulangClosure.PaperTypes.PaperCoreStep.choose_applicable,
    `YulangClosure.PaperTypes.PaperCoreStep.absurd_no_step,
    `YulangClosure.PaperTypes.PaperCoreStep.preservation,
    `YulangClosure.PaperTypes.PaperCoreControl.controlStep_evidence,
    `YulangClosure.PaperTypes.PaperTypeApplicationPreservation.mapDeclarationTable_cancel,
    `YulangClosure.PaperTypes.PaperTypeApplicationPreservation.instantiate_body,
    `YulangClosure.PaperTypes.PaperTypeApplicationPreservation.typeBetaValue_preservation,
    `YulangClosure.PaperTypes.PaperTypeApplicationPreservation.force_typeBeta_delay,
    `YulangClosure.PaperTypes.PaperTemplateExecution.BodyTyped.instantiate,
    `YulangClosure.PaperTypes.PaperTemplateExecution.BodyTyped.expand,
    `YulangClosure.PaperTypes.PaperTemplateExecution.template_applicable,
    `YulangClosure.PaperTypes.PaperTemplateExecution.template_preservation,
    `YulangClosure.PaperTypes.PaperCombinedExecution.finite_interaction,
    `YulangClosure.PaperTypes.PaperCombinedExecution.shared_continuation_prefixes,
    `YulangClosure.PaperTypes.PaperCombinedExecution.example_arbitrarily_many_rounds,
    `YulangClosure.PaperTypes.PaperExtendedExecution.preservation,
    `YulangClosure.PaperTypes.PaperExtendedExecution.finite_interaction,
    `YulangClosure.PaperTypes.PaperExtendedExecution.mixed_preserved,
    `YulangClosure.PaperTypes.PaperEliminationExamples.choose_false_rejects_right,
    `YulangClosure.PaperTypes.PaperEliminationExamples.choose_true_rejects_left,
    `YulangClosure.PaperTypes.PaperEliminationExamples.type_beta_choose_return
  ]
  let env ← getEnv
  for name in #[
    `YulangClosure.PaperTypes.PaperComputationTyped.chooseLeft,
    `YulangClosure.PaperTypes.PaperComputationTyped.chooseRight,
    `YulangClosure.PaperTypes.PaperComputationTyped.absurd
  ] do
    match env.find? name with
    | some (.ctorInfo _) =>
        logInfo m!"YULANG_AUDIT_CONSTRUCTOR {name}"
        let id := mkIdent name
        elabCommand (← `(#check @$id))
        elabCommand (← `(#print axioms $id))
    | _ => throwError "required typing constructor is missing: {name}"
  let mut targets : Array Name := #[]
  for moduleName in modules do
    let some moduleIndex := env.getModuleIdx? moduleName
      | throwError "audited module is not imported: {moduleName}"
    let mut count : Nat := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some moduleIndex then
        match info with
        | .thmInfo _ =>
            unless !targets.contains name do
              throwError "duplicate theorem target: {name}"
            targets := targets.push name
            count := count + 1
        | .axiomInfo _ => throwError "project axiom in audited module: {name}"
        | _ => pure ()
    if count == 0 then
      throwError "audited module has no theorem declarations: {moduleName}"
    logInfo m!"YULANG_AUDIT_MODULE {moduleName} {count}"
  for root in roots do
    unless targets.contains root do
      throwError "required root is missing or is not a theorem: {root}"
  for name in targets do
    logInfo m!"YULANG_AUDIT_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_AUDIT_END {name}"
  logInfo m!"YULANG_AUDIT_COUNT {targets.size}"
