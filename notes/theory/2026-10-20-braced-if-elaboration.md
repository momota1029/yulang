# R135: conditional elaboration of braced conditional arms

Status: **CANDIDATE CONDITIONAL SOURCE CORRESPONDENCE; NOT INDEPENDENTLY REVIEWED.**
Assignment: R135 proof, revision 1. Author: `/root/r135_braced_if_proof`.
Frozen contract: `tasks/agent-loop/sprints/braced-if-adoption-20261020-r135-rev2.md`,
SHA-256 `ff13b7215e4b04e30a2c0bc49ddc177b5a6caf2b57bd105275344eadf74edaa7`.
Baseline reported by Luna: `94bd0aee28508a3316635e6f286a13f153598405`,
branch `research/simple-sub-intrusion`.

## Parent claim and authority boundary

The parent asks whether dedicated braced `IfArm`/`ElseArm` expression lists can elaborate to existing Y3 conditionals while preserving colon forms, condition/body ownership, arm order, scope, effects, recovery, source provenance and runtime meaning. Its source domain includes the oracle's empty, multi-item and spread-bearing lists; this note does not narrow that domain. The exact 388-byte fixture `web/playground/examples/yulang2-ordinary-islands.yu`, especially its singleton countdown arm bodies, is the motivating application. Expected selected result `countdown_result -> 8` is an acceptance obligation, not an observed result.

The current syntax reference and Authoritative architecture require colon bodies for `if`/`elsif` and explicitly defer brace adoption. Proposed braces must use dedicated comma/semicolon-separated expression-list grammar/CST with spread; ordinary `BracedStatementBlockExpression` and `braced_statement_block_normalized` are excluded. Y2 acceptance is historical evidence, not Y3 semantic authority. Only user approval after fresh review can authorize adoption and a successor implementation contract.

This is a constructive conditional representation argument plus an attributed source audit. It is neither an approved syntax amendment nor an established theorem of actual new source construction, inference or native execution. Original Simple-sub/evaluator A/B, source/native, R85 and production gates remain OPEN. No inference rule, constraint generation/accumulation, propagation, level, extrusion, qualifying intrusion or generalization change is proposed.

## Evidence provenance and frozen inputs

The author made one read-only `cat` invocation for entry rules, skills and the frozen contract before noticing that this packet prohibits commands. Its combined output was truncated. The author then stopped commands and requested source facts from Luna. No Git, build, test, formatter, browser, compiler command, nested CLI or production mutation ran in this assignment. The source facts below were supplied by Luna from primary inspection; they are not represented as this author's independent source inspection or pin verification. Fresh reviewers must inspect the actual pinned owners.

Luna reported baseline/branch/upstream equality and clean entry worktree, with inherited UNKNOWN leases untouched, and subsequently confirmed all required direct source-owner hashes and the rev2 contract hash at this frozen seam. Required direct pins and the additional historical lowerer dependencies are listed below. The contract and primary-supplied facts, rather than uninspected historical proof claims, are the premises of this note.

| Dependency | SHA-256 |
| --- | --- |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `syntax-reference/en/src/expressions/if-expression.md` | `2b929dcdd31587c1ed5f0b0569cfc41e2f2bc29bf04a5f21be06bf24620718f3` |
| `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `crates/yu-syntax/src/expression/if_expr.rs` | `509af68c34e11a2a2d5538df8bab84c599d68154a3f03d57c304bbfb04d8cd39` |
| `crates/yu-syntax/src/statement.rs` (comparison only) | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |
| `crates/yu-hir/src/module/local_source.rs` | `d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |
| `web/playground/examples/yulang2-ordinary-islands.yu` | `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487` |
| `crates/yu-hir/tests/conditional_local_source.rs` (regression contract only) | `1a271192071dc3c690080802c69ad63246f631f7a9039b4200c40fbffb139c40` |
| Y2 `spec/2026-06-06-syntax-design.md` | `55255c6d7caf16c93098f5a0437ac91136250e36d1872ce0546d2f4b2d6a83bd` |
| Y2 `crates/parser/src/expr/control.rs` | `0102f9e8c6ded9c03c51a71356a1532a9db8742de181d649f642ad9d325f4e5b` |
| Y2 `crates/parser/src/expr/group.rs` | `bb58bd49ec272003e69d4675c2d6ee1de470e3c1ebaed0f632b6f117629acf38` |
| Y2 `crates/infer/src/lowering/control.rs` | `4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963` |
| Y2 `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |

All Y2 paths resolve under `/home/momota1029/rust/yulang2-oracle-capture`. Additional reported routing through Y2 `lowering/expr/chain.rs` and the Y3 `tools/inference-playground/src/lib.rs` run path has no supplied full file pin; those facts are explicitly provisional locators, not extra frozen authoritative dependencies. Authors of historical source files were not supplied: UNKNOWN. No historic proof is imported.

## Actual constructor and consumer facts

1. Y3 `if_arm_normalized` stops the condition at `Colon | LeftBrace | Elsif | Else`, but accepts only `Colon` as a body introducer. It then calls `colon_body_normalized`; otherwise it produces `missing_if_arm`. Therefore an existing stop at a brace does not prove a braced arm is constructed.
2. Y3 `else_arm_normalized` uses `colon_body_normalized` for a colon and `inline_body_item_normalized` for another non-boundary expression item. A left brace currently takes the ordinary expression route. This must be distinguished from the dedicated proposed else-body constructor.
3. Y3 `Builder::conditional` recognizes `OperatorChain | IndentedStatementBlock` bodies for `IfArm` and `ElseArm`, builds `LocalSourceForm::If { arms, else_branch }`, retains arm order, and lowers the condition/body children in the enclosing lexical scope. A new dedicated arm-list child is not currently a recognized body.
4. `Builder::expression` routes ordinary `BracedStatementBlockExpression` to `block()`; that lowerer handles bindings/initializers and a final `OperatorChain`, with private local visibility. This is evidence against casually reusing that outer grammar/CST as the requested expression list.
5. The runtime program consumer maps `LocalSourceForm::If` arm/body labels to `Instruction::If`. The machine evaluates the first condition, pushes `Frame::Condition`, and selects a body. These are the existing downstream consumers to preserve, not a proof that an unimplemented new parser/HIR path reaches them.
6. The reported playground run path passes the LocalSource model to `CandidateInference::solve`. No supplied exact internal solver constructor/consumer establishes the desired all-arm value/effect constraints. The test file is only a regression contract, never the HIR owner or an inference proof.

## Conditional singleton elaboration lemma

Fix any ordered conditional with finitely many arms `(c_i, b_i)` and optional else body `b_e`. Quantify independently over every condition, every branch expression, lexical environment, source identity and runtime continuation; do not assume one chosen condition outcome or identify branch effects.

Assume:

- **P1 — source construction:** a dedicated arm parser constructs exactly one `IfArm`/`ElseArm` expression-list child for each proposed braced body, owns both delimiters and separators, and returns the following outer `elsif`/`else` boundary to the original conditional. The existing `Condition` owns exactly `c_i`.
- **P2 — singleton body elaboration:** for a list whose sole supported item is expression `b`, its dedicated HIR body consumer lowers that same expression in the existing enclosing lexical scope, with no wrapper evaluation, extra binding, visibility change or added type/effect operation. It records the enclosing arm/body owners and each original condition/expression source key without conflating them.
- **P3 — representation preservation:** the resulting `LocalSourceForm::If` has the same ordered condition/body child graph as the existing conditional representation, up to an injective renaming of source-node identities that retains each node's own original CST provenance. The optional else is preserved exactly.
- **P4 — downstream invariance:** inference and execution depend on the preserved conditional graph and its expression meanings; metadata remapping preserves all diagnostic/source lookups. This is a separate inference/source premise, not established by this note.

Then singleton brace syntax introduces no additional conditional evaluation operation beyond the existing If consumer. For each arm P2 supplies the existing expression body, P3 puts it in the same ordered graph slot, and the runtime program consumer therefore produces the same `Instruction::If` arm/body-label graph up to label renaming. Each corresponding execution step reads the corresponding condition/body instruction and resumes the corresponding continuation; whenever that condition evaluates to a branch-selection result, both graphs select the same slot. Induction over those existing machine steps preserves the graph correspondence.

This representation argument is parametric in every branch and continuation. It neither derives termination nor proves boolean checking, complete evaluator correctness or effect soundness. It does not infer any foreign-continuation theorem from a single `Frame::Condition` action. Under P4 the same input conditional graph permits reusing an independently established inference law; that inference law itself is still missing here.

The lemma applies directly to the singleton shape identified by Luna in the unchanged countdown source: after P1–P4 are independently discharged, braces need no new runtime conditional instruction. It reduces the required successor work to actual dedicated source construction, dedicated HIR recognition and preservation evidence. It does not establish the countdown's full parse, iteration/arithmetic behavior, termination or result 8. It does not discharge empty/multi-item/spread cases.

## Y2 body-value audit and the remaining Y3 semantic gap

The reported Y2 control parser chooses colon inline/indent or a delimited `BraceGroup`; group parsing uses an `ExprListMachine`, comma/semicolon separators and `allow_spread = true`. Y2 `lower_if_arm_body` invokes `lower_expr`. The reported chain routing sends a non-record `BraceGroup` to `lower_expr_block`. This is a consumer chain, not an argument that a brace group means a statement block in Y3.

| Parsed arm-list case | Reported Y2 consumer behavior | What is established for Y3 |
| --- | --- | --- |
| Empty | The block lowerer returns unit. | No approved dedicated arm-list-to-unit rule. Open adoption/consumer premise. |
| One supported `Expr` | The expression is the tail result. | Conditional lemma above; actual new constructor/recognizer absent. |
| Multiple supported items | `block_lowering_items` selects `Binding | Expr | ForStmt`; `lower_block_items` runs preceding selected items then uses a tail `Expr`. Exact typing/effect behavior depends on the actual selected item cases. | No approved expression-list sequence/value/effect elaboration. Do not import statement grammar or infer arbitrary tail behavior. |
| `ExprSpread` | Parser admits it; the reported block-item filter omits it. | Source-to-consumer gap already in the historical oracle path; neither spread evaluation nor effect preservation follows. |

Y2 `lower_if` reportedly visits every arm and lowers its condition/body, subtype-joining body values/effects into result variables; a conditional without else discards arm values, while an else branch participates in the result join. This is evidence about Y2 only. It does not prove equivalent Y3 inference, especially for omitted spread expressions or a new sequence representation.

A source-qualified falsification target is an otherwise accepted brace arm containing a spread of an effectful expression: admission by `ExprListMachine` plus omission by `block_lowering_items` would defeat any claimed “all parsed items preserve value/effect” bridge. This is a static candidate counterexample method, not an executed counterexample; full source reachability and resulting diagnostic/runtime behavior have not been checked. Owning symbols are Y2 `ExprListMachine`, `lower_if_arm_body`, `lower_expr`, `lower_expr_block`, `block_lowering_items` and `lower_block_items`. The unpinned chain-routing detail requires reviewer confirmation.

Thus the parent remains OPEN for its original domain. Settling the empty/list/spread behavior requires Luna's authority process and any necessary user decision before a Y3 implementation, not silently filtering syntax or adopting a historical accidental omission.

## Recovery, ownership and preservation obligations

P1 is not proved from a hypothetical parser transition. Existing brace stops merely identify a possible seam. Exact missing cases are horizontal/newline arm association; nested braces and nested if/dangling else; missing/mismatched close; empty body; malformed condition; malformed nested item; trailing tokens; and avoidance of duplicate Missing/Error products or consumption of an outer close. Owners are `if_arm_normalized`, `else_arm_normalized`, the proposed dedicated arm-list parser and their enclosing conditional boundary consumer.

P2/P3 require each arm key, condition key, body key and item key to remain distinct. “Same graph” does not mean equal source offsets between differently spelled colon and brace programs. The new source must retain its own exact ranges and constructor identities. The outer brace owner cannot be replaced by a generic statement-block key, and condition/body or provider/residual/witness identities cannot be collapsed to make correspondence easier.

Colon-inline, colon-indented and existing bare else forms require unchanged-path evidence; the brace arm must be selected at its own introducer before ordinary else expression fallback. Earlier condition stop-set behavior alone gives no proof of no regression. All inference arms must continue generating/accumulating their ordinary constraints and effects, including unselected runtime branches. That preservation obligation belongs to the actual inference owner behind `CandidateInference::solve`, whose precise internal symbol was not supplied.

## Minimal successor TODO and exact falsifiers

This packet authorizes no implementation. After user approval and a fresh exact lease, the minimal provisional or approved implementation seam is: dedicated arm-list construction at `if_arm_normalized`/`else_arm_normalized`; explicit dedicated body recognition in `Builder::conditional`; source-key mapping; reuse of the existing `LocalSourceForm::If`/runtime consumers only when the independently approved list elaboration supplies their bodies. If the chosen list semantics requires a new type/effect/runtime operation, return to Luna before writing that operation.

Falsifiers are changed condition extent; an inner parser consuming an outer close or outer arm; incorrect arm association/order; lost or conflated keys; new lexical visibility; changed body value/effect or omitted spread effect; inference skipping an arm; different missing/error recovery products; existing colon regressions; and an actual unchanged countdown witness that fails or does not select result 8. No tests of assumed parser/HIR transitions can establish that the real owners emit them.

Luna TODO: decide the empty/multi/spread semantic gap through the existing authority process; freeze the complete solver/chain dependencies; assign fresh independent review; preserve R132's failed parse and all parent gates. Future implementation owner TODO: discharge P1–P3 on actual constructors and provide whole-fixture parser/HIR/inference/runtime evidence. Future inference/source reviewer TODO: locate actual all-arm value/effect consumers behind `CandidateInference::solve`, verify P4 and recovery/source provenance. This author cannot certify those results.

## Resources and stop receipt

Requested assignment: prover, Sol/high, at most 360 seconds, zero descendants/Astra. Observed task identity: `/root/r135_braced_if_proof`; runtime UUID, actual model and actual effort: **UNKNOWN**. A role request is not a model observation. First explicit clock observation: `2026-10-19 22:13:57 UTC`; final clock/elapsed receipt is in the handoff. No tests or executable verification ran. Checks were a conditional derivation and primary-attributed static source facts, with the one accidental read command disclosed above.

Only this note and `tasks/agent-loop/inbox/20261020-r135-proof.md` are leased outputs; no scratch files or descendants. Freeze this revision for Luna intake and fresh review. **STOP / NO_DESCENDANTS.**
