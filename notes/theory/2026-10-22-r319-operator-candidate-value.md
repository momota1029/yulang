# R319 — operator RHS as a candidate value

Status: OPEN. No source/operator inference theorem or production gate is discharged here.

## Parent and direct evidence

The parent remains the unchanged Yulang2 playground examples running through ordinary inference and execution, with source/native proof obligations complete. R316–R318 now retain the imported `+` owner's exact provider RHS expression in the candidate module world. The remaining failure is at the candidate value boundary.

Three source owners expose the current gap:

1. `candidate_imported_definitions` in `crates/yu-solver/src/shadow_apply.rs` builds imported callable routes only from resolved `SourceExportId` values to provider `DefId`s. Operator declarations have a distinct `SourceOperatorOwner` receipt.
2. Candidate scheme capture is scheduled over `ConstraintBatch.definitions`, whose records and `DefinitionOrderId`s are created for `HirItem::Binding`. `candidate_scheme::GraphState.graphs` is sized from that binding list; selected operator RHS expression roots have value/effect occurrence components but no generalized candidate graph slot.
3. `emit_candidate_source` in `crates/yu-solver/src/candidate_source.rs` explicitly returns unavailable for `LocalSourceForm::InfixOperator`; it emits no Apply relation for its left and right operands.

`ClosedSchemes::for_root` in `crates/yu-solver/src/shadow_f5.rs` exposes legacy finalized F5 schemes by `DefinitionRootId`; it is corroborating evidence of that API boundary, not the central candidate blocker. The candidate blocker is the missing source-root-indexed graph/generalization lifecycle for an `ExpressionRootId`. A fabricated `DefId` or `DefinitionOrderId` would hide that construction gap and is excluded.

## Candidate construction target

Use the existing exact provider expression root as the source of one operator value scheme. Resolve each consumer use by its authenticated `SourceOperatorOwner`, then instantiate that scheme independently at the use. For strict infix `+`, preserve left/right order and express the result through two ordinary Candidate Apply relations so the existing AV/AE/RE/RV and effect machinery remains the owner of application behavior. The original operator use occurrence must own the combined result and retain both operand edges.

This is an implementation target, not yet a proof. The exact scheme-owner representation still needs to be selected from existing typed identities or extended with a constructional source identity. Do not change the language contract, introduce a stdlib spelling special case, or claim generalization until the implemented path and independent review establish it.

## Source-backed dependency ordering

The scheme-owner gap is downstream of the current F0/F1 dependency graph. `DefinitionUse.target` is a `DefinitionOrderId`, and `SccPlan` indexes only collected binding definitions. The candidate graph executor captures those dependency-first binding components before member graphs. `InferenceSession::execute` runs module-expression schedules only after `execute_scc_plan`. Therefore capturing an operator RHS as a late expression graph cannot supply a generalized value to an earlier infix use.

The next code step must admit exact operator owners as source-backed scheme dependencies in the same ordering that makes their graph available before each consumer. Preserve the imported `SourceOperatorOwner`, provider `ExpressionRootId`, and consumer occurrence as distinct identities. Do not encode the operator as a fabricated `DefId`/`DefinitionOrderId` or treat the infix as an ordinary Name use.

## Verification boundary and next step

R318's exact module/root projection remains verified. The next implementation seam is the source-backed dependency plan: add an exact operator scheme owner and provider edge so its graph is captured before consumers, then route each authenticated operator use through independent FreshUse. Then `candidate_source.rs` can emit two ordered Apply relations whose source owner is the original infix occurrence. Focused evidence must show argument, result, and effect ports survive both applications and two uses receive distinct instances. Existing ordinary imported-name Apply tests must continue to pass.

The original source-generation A/B theorem, principality, all fixity/laziness combinations, runtime evaluation, R149, and production remain OPEN. No independent review ran; the current implementation and source mapping require fresh review before any gate promotion.
