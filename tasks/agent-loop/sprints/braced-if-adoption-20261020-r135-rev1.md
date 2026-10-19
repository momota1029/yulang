# Sprint: braced `if` compatibility proposal — R135 rev1

Status: **DRAFT_FIXED_OUTCOME; no compiler implementation authority**  
Branch: `research/simple-sub-intrusion`; frozen baseline `94bd0aee28508a3316635e6f286a13f153598405`  
Goal: prepare an independently reviewed, user-decision-ready narrow addendum for the exact unchanged Yulang2 countdown fragment. The broad parent goal remains proof-backed inference/evaluator breadth and the widest practical unchanged-demo coverage.

## Fixed outcome

Specify whether and how Yulang3 may accept braced `if` / `elsif` / `else` arm bodies while preserving existing colon-form behavior, source ownership, conditionals, branch effects, recovery boundaries and existing runtime meaning. Use the exact 388-byte shared source `web/playground/examples/yulang2-ordinary-islands.yu`, especially the unchanged countdown expression on line 12 and result on lines 13–14, as the motivating witness. Do not rewrite it, implement brace acceptance, retry a Web check, or claim countdown support in this sprint.

The deliverable may reach **Reviewed** only. Existing grammar says `if` and `elsif` require colon-introduced bodies. Only explicit user approval can make a reviewed amendment **Authoritative** and authorize a successor implementation sprint. R132 remains `CLOSED_FAILED`; its failure is preserved.

## Baseline, authority and source pins

Baseline commit: `94bd0aee28508a3316635e6f286a13f153598405`; branch must remain `research/simple-sub-intrusion`. Startup evidence: clean worktree, HEAD and upstream equal at baseline, all listed historical agents terminal; inherited UNKNOWN workers, board quarantine and reservations remain untouched.

Governing authority:

- `rules/design-authority.md`, especially approval / supersession gate.
- `syntax-reference/en/src/expressions/if-expression.md`, §2 accepted syntax and §4 direct CST; brace arm bodies are outside scope.
- `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`, current conditional and braced-statement ownership sections, including the explicit brace-body deferral.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` for inference behavior and proof direction.
- Frozen Yulang2 oracle `spec/2026-06-06-syntax-design.md` §§if / brace list and `crates/parser/src/expr/{control.rs,group.rs}` as accepted-input evidence only.

Direct owners and pins at contract creation: `if_expr.rs` `509af68c34e11a2a2d5538df8bab84c599d68154a3f03d57c304bbfb04d8cd39`; `statement.rs` `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797`; `local_source.rs` `d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442`; `conditional_local_source.rs` `1a271192071dc3c690080802c69ad63246f631f7a9039b4200c40fbffb139c40`; runtime `program.rs` `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d`; runtime `machine.rs` `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd`; exact demo fixture `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`; oracle if parser `0102f9e8c6ded9c03c51a71356a1532a9db8742de181d649f642ad9d325f4e5b`; oracle group parser `bb58bd49ec272003e69d4675c2d6ee1de470e3c1ebaed0f632b6f117629acf38`; oracle spec `55255c6d7caf16c93098f5a0437ac91136250e36d1872ce0546d2f4b2d6a83bd`.

No parser/HIR/runtime source, tests, Web selectors, oracle expectations or generated artifacts may be edited. No test, build, CLI, formatter, or browser command is authorized. No source/API/syntax adoption, semantic review decision, test-contract change, parent-gate promotion, or Git action is included.

## Questions and falsifiers

The proposal must answer:

1. Can a brace opener after a completed condition enter a brace-body parser while the existing `Condition` still owns exactly the original condition and the matching `}` remains owned by the brace parser?
2. Can colon-inline, colon-indented, and proposed braced expression-list bodies lower through an explicit new owner representation while preserving each arm's source keys and lexical scope, retaining all-branch inference and branch order?
3. How do `elsif` / `else` associate across horizontal whitespace, newlines, nested braces and nested `if`, including dangling-else cases? Which exact boundary returns `elsif`/`else` to the outer `IfExpression`?
4. What recovery products result for missing/mismatched close, empty body, malformed condition, malformed nested statement and trailing tokens, without adding duplicate Missing/Error nodes or consuming an outer close?
5. Do existing effect typing and `Instruction::If` / `Frame::Condition` execution remain unchanged after structural HIR elaboration?

The current Authoritative architecture explicitly excludes sharing `BracedStatementBlockExpression` with if arms and calls for a dedicated expression-list grammar/CST owner. The proposal must preserve that distinction; it must not route braces through `braced_statement_block_normalized` or reinterpret expression-list items as statements. Falsifiers include altered condition extent, close ownership or `else` association; body statements gaining a different lexical scope; changed branch order/value/effect; lost source occurrence/key; changing the Yulang2 arm-list contract; HIR/runtime semantic changes; or a parser-only change that leaves LocalSource unable to form the original conditional. If any requires a distinct language or runtime decision, return it for separate approval.

## Lanes and exact output leases

**Constructive syntax-to-consumer proof lane (prover, Sol/high, max 360 seconds):** only `notes/theory/2026-10-20-braced-if-elaboration.md` and `tasks/agent-loop/inbox/20261020-r135-proof.md`. Establish the conditional correspondence from a dedicated expression-list arm CST constructor through LocalSource arm ownership to the existing If consumer/runtime. State exact conditional premises and unresolved adoption, recovery and source/native obligations. Do not assume statement-block reuse. No implementation or commands.

**Primary design / implementation planning lane (Luna/high, max 180 seconds):** only `notes/design/2026-10-20-braced-if-compatibility.md` and `tasks/agent-loop/inbox/20261020-r135-implementation.md`. Specify a concrete accepted-input envelope, dedicated arm/CST shape, expression-list grammar ownership, recovery ownership, unchanged HIR/runtime law, tests, integration order and rollback. Keep it Draft pending review and user decision.

The primary owns this contract and `tasks/agent-loop/current.json`. No overlapping paths. Fresh independent spec and compiler/source reviewers inspect the frozen proposal/proof/handoffs; authors do not review their own artifacts. Any finding is fixed only in a sequential new revision, with prior receipts preserved.

## Verification and resources

Cap 1,200 seconds total: inventory 120, authority/source analysis 180, proof 360, design/planning 180, independent reviews 240, closeout 120. Zero Astra; at most one heavy process. Preserve all existing UNKNOWN identities, quarantines, leases and resource reserves. No substitute workers unless supported runtime receipts and exact leases are recorded.

Success is a reviewed proposal with the exact Yulang2 source/result, explicit alternatives and user approval boundary, plus an independently reviewed conditional correspondence. No executable verification is run in R135. A future implementation contract must be issued only after the user approves the addendum; it must pin fresh source and include parser, HIR, inference, diagnostics, CLI and Web evidence, with the unchanged entire shared fixture and its expected selected result `countdown_result -> 8` as acceptance tests. Original Simple-sub/evaluator A/B, source/native, R85 and production gates stay OPEN.

## Stop conditions

Stop before writing if branch/HEAD/worktree differ, any required owner pin changes, unresolved existing ownership overlaps, a needed source owner is absent, or the brace handoff needs a new runtime/type/effect rule. Stop after review if any BLOCKING/major finding remains. Do not claim countdown works; do not reopen R132 or R133; preserve all prior failures.
