# R135 implementation planning handoff, rev1

Sprint / contract: R135, `tasks/agent-loop/sprints/braced-if-adoption-20261020-r135-rev2.md`, SHA-256 `ff13b7215e4b04e30a2c0bc49ddc177b5a6caf2b57bd105275344eadf74edaa7`.

Outcome: primary-authored post-approval implementation plan. This is not an implementation lease. Current authority remains colon-only for `if` / `elsif`; no parser, HIR, test, CLI, Web or runtime path is authorized before explicit user approval of a reviewed addendum.

Parent outcome: run the unchanged `web/playground/examples/yulang2-ordinary-islands.yu` countdown path through the existing selected-definition API and continue expanding unchanged Yulang2 sample coverage. R132 is `CLOSED_FAILED` at brace-form `if` parsing; preserve its exact failure and do not retry it in this proposal sprint.

Source-to-consumer path to implement only after approval:

`IfExpression parser -> dedicated brace-arm expression-list CST -> Builder::conditional -> existing LocalSourceForm::If -> CandidateInference -> RuntimeProgram::Instruction::If -> Machine::Frame::Condition -> execute -> WASM/Web`

The arm brace CST must be a dedicated owner directly within `IfArm` / `ElseArm`. It must not reuse ordinary `BracedStatementBlockExpression` or `statement::braced_statement_block_normalized`. `Builder::conditional` currently accepts only `OperatorChain | IndentedStatementBlock` arm bodies, so parser-only work cannot make the exact source executable. The selected implementation must decide whether a dedicated body is represented as an ordinary sequence, a new `LocalSourceForm`, or another reviewed structure; do not equate an expression list with the existing statement block without source-level correspondence.

Post-approval work order:

1. Parser syntax/CST addendum under `crates/yu-syntax/src/expression/if_expr.rs` and a dedicated expression-list owner. Reuse only lower-level scanning/list primitives after proving the separator, spread and close policies match. Preserve current colon form and arm continuation.
2. Structural/recovery tests in `crates/yu-syntax` for `if`, `elsif`, `else`, nested/dangling `else`, horizontal/newline continuation, brace close ownership, empty/multi-item/spread cases and malformed boundaries. Expected output is additive; do not alter current oracle expectations.
3. HIR carrier in `crates/yu-hir/src/module/local_source.rs` and focused `crates/yu-hir/tests/conditional_local_source.rs` coverage for arm order, condition/body source identity, enclosing lexical scope, all supported body cardinalities, and rejection of unrelated statement/record forms.
4. Focused candidate inference tests to show the existing conditional joins every condition/body with unchanged effect and value ownership. The Y3 solver's all-arm/effect correspondence is not proved by existing LocalSource construction alone.
5. Exact unchanged source CLI regression selecting `countdown_result -> 8`, followed by the existing Web/WASM `npm --prefix web/playground run check`, only after final reviews are CLEAN and each predecessor passes.

Hard decision input before implementation: Y2 parser accepts `ExprSpread` in brace groups, while its inspected `lower_if_arm_body -> lower_expr -> lower_expr_block` path obtains items through `block_lowering_items`, which filters `Binding | Expr | ForStmt`. The inspected source does not establish a useful Y2 spread result in this context. The successor contract must either explicitly reject spread before semantic lowering or approve and prove a full spread meaning; it must not silently omit spread. Empty-list unit and ordinary multi-item sequencing have Y2 implementation evidence but require a dedicated Y3 source/HIR correspondence.

Falsifiers: non-dedicated statement-block body; altered condition/brace/`else` ownership; lost source identity/order/scope; branch value/effect difference; parser recovery that consumes an outer close or changes colon-form output; unsupported spread silently disappearing; or exact `countdown_result` mismatch. A failure stops the affected contract at its first gate. No claim here closes R64/R65, source/native, Simple-sub/evaluator A/B, effect-hygiene, or production gates.

Exact owner baseline pins and source routes are in contract rev2. Proposal/design artifact: `notes/design/2026-10-20-braced-if-compatibility.md`. Proof owner: `notes/theory/2026-10-20-braced-if-elaboration.md` and `tasks/agent-loop/inbox/20261020-r135-proof.md`. Proposed future code paths are not currently leased.

---

## Luna correction handoff rev2 — R135 rev4

The rev1 plan is retained as history, but its Y2 body account is **NOT CLEAN**. Fresh compiler/source review found that `lower_expr` first applies `brace_group_is_record_literal`; only a non-record `BraceGroup` reaches `lower_expr_block`. The previous claim that empty brace bodies yield unit and the general statement that spread is omitted are withdrawn.

The corrected design separates the exact shapes: empty record; field/record-shaped expression; record-spread group; non-record singleton; non-record multi-item; mixed non-record spread; separator-only and malformed input. The new oracle pins and exact dispatch are in R135 rev4. Mixed-spread omission is limited to block-item filtering; record spread has an `Expr::Record` consumer and effect join. Countdown's two singleton bodies remain a conditional target, with no acceptance or execution claim.

The Y3 bare `else {` path also needs precise wording: `inline_body_item_normalized` detects `LBrace` as an inline boundary, emits Missing and returns the brace to its owner; it does not accept a normal brace expression as the else body.

Revision 2 recommends that the eventual user choice be explicit between narrow singleton countdown compatibility (with an explicit disposition for every other brace shape) and shape-compatible historical dispatch. Neither is selected here. The proposal remains Draft, the existing grammar remains colon-only, and no implementation lease exists. The INDEX Draft/unapproved locator was added after the spec-review MINOR.

R135 rev4 contract: `tasks/agent-loop/sprints/braced-if-adoption-20261020-r135-rev4.md`, SHA-256 `971fc2692374ef3feadf344a3a4e6fa6d936c9da838879f3f2b78c6e7803143a`. Fresh independent delta review is required for this correction package.

---

## Luna correction handoff rev3 — R135 rev5

R135 rev4 was independently reviewed and remains **NOT CLEAN** with two MAJOR findings. The design and proof audit now state the full `brace_group_is_record_literal` predicate: recognized Expr/ExprSpread children must pass their child checks, Separator is allowed, every other child kind returns false, and the final condition is `has_item || !saw_child`. This is only a dispatch predicate; parser reachability and downstream malformed-shape behavior remain separate.

Record dispatch is also separated from successful lowering. Multiple valid spread operands can pass the predicate, but `lower_record_literal` rejects the second spread before lowering that operand. A successful record path requires at most one spread plus valid field/operand processing. The design makes no claim about whether the first operand was lowered on the rejected path.

No Y3 choice follows. The proposal remains Draft, current syntax remains colon-only, and no implementation lease exists. The conditional singleton lemma still depends on actual route and P1–P4. INDEX remains unchanged with its Draft/unapproved locator.

R135 rev5 contract: `tasks/agent-loop/sprints/braced-if-adoption-20261020-r135-rev5.md`, SHA-256 `6f263805f1cf81c436caaa96ad87889f7e1c0d25a46d5a957cafed1ea0b969de`. The rev4 spec/compiler MAJOR receipts remain immutable; both original reviewers own only focused rev5 delta reviews.
