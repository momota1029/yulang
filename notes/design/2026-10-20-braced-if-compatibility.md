# Braced `if` arm compatibility proposal

Status: **Draft; rev3/rev4 source-accounting findings are being corrected; not ready for user approval**  
Scope: Yulang2 accepted brace-form `if` / `elsif` / `else` arm bodies and the source path needed to execute the unchanged countdown example. This proposal does not change branch typing or runtime semantics.  
Drafted-by: Luna primary, R135  
Supersedes: none until user approval is recorded

## Why this proposal exists

The unchanged Web playground sample contains:

```yu
my countdown flag = if flag { 8 } else { countdown true }
our countdown_result = countdown false
countdown_result
```

The Yulang2 parser accepts the braces as expression-list bodies. Yulang3 currently requires `:` after an `if`/`elsif` condition, and the unchanged source fails before inference. R132 recorded this failure and is closed; this proposal does not retry it or claim the countdown result.

The current Yulang3 `if` specification requires colon bodies. The 2026-08-20 syntax architecture explicitly deferred brace arms to a dedicated expression-list grammar and CST owner. It also says not to share the outer `BracedStatementBlockExpression` with `IfArm` / `ElseArm`. Any change therefore needs a reviewed addendum and explicit user approval before parser or HIR implementation.

## Yulang2 evidence

The frozen Yulang2 grammar accepts:

```text
if / elsif: Condition (Colon InlineOrIndentBody | LeftBrace ExprList? RightBrace)
else:        Colon InlineOrIndentBody | LeftBrace ExprList? RightBrace | Expr
```

`parse_if_arm` stops the condition at colon or `{`; `{` enters a brace-owned `BraceGroup`. The group parser uses comma/semicolon expression-list separators and enables `ExprSpread`. Newline arm continuation remains owned by the containing `IfExpr`; only `elsif`/`else` at the `if` base indent or deeper continues that expression.

The Yulang2 consumer is shape-sensitive. `lower_if_arm_body` calls `lower_expr`, but that does not imply every `BraceGroup` reaches block lowering: `lower_expr`'s brace dispatch first applies the record-literal guard. The frozen oracle source audit found these paths:

The pinned predicate walks child nodes as follows: an `Expr` child qualifies only if it is an inline record field; an `ExprSpread` qualifies only if it contains an `Expr` child; `Separator` is permitted; every other child kind, including any `Missing`/error-shaped child, returns false. Its final result is `has_item || !saw_child`. Predicate result only selects the record path: it does not establish that the parser produces the shape or that record lowering succeeds. Genuinely empty has no children and returns true; separator-only has children but no qualifying item and returns false.

| Brace-group shape | Yulang2 route and observed meaning | Yulang3 proposal status |
|---|---|---|
| Empty `{}` | The record guard accepts a genuinely empty group. `lower_record_literal` constructs an empty record (`Pos::Record([])` / `Expr::Record`); it does not produce unit. | No compatibility meaning selected. Empty-as-unit would be a deliberate difference requiring user approval. |
| Record-shaped fields, including `{ field: value }` | The record guard routes the group to record lowering. A singleton field group is not a generic singleton expression list. | Record-vs-list interpretation is an explicit design boundary; the dedicated owner cannot silently erase record behavior. |
| One-spread-only `{ ..r }` | The record guard accepts a spread with an `Expr` operand. Record lowering can lower one spread operand, join its effect and construct record-spread semantics, subject to operand/field checks. | No blanket spread rejection or omission claim. A different Y3 rule needs explicit approval. |
| Two or more operand-bearing spreads | The record guard can accept all such children, but `lower_record_literal` rejects the second spread before lowering that operand. Predicate acceptance does not imply successful record construction. | Duplicate-spread behavior is undecided for Y3 and requires an explicit rule. |
| Non-record singleton expression | After the record guard fails, the group reaches block lowering. The exact selected-item/tail result must be stated only for the source forms admitted by that route. | Countdown's `{ 8 }` and `{ countdown true }` need a dedicated singleton correspondence; they do not establish general list semantics. |
| Non-record multi-item / mixed spread | After the record guard fails, block lowering uses `block_lowering_items`; that filter includes `Binding`, `Expr`, and `ForStmt`, and may omit spread items. This omission is limited to this non-record block path. | Mixed-spread treatment remains unresolved; the earlier general “spread gap” claim is withdrawn. |

These are inspected Yulang2 implementation paths, not new Yulang3 rules. Unexpected child kinds make the predicate false, but parser reachability and downstream block-lowering/recovery behavior remain unestablished for malformed shapes. Field/operand validity and at-most-one-spread are additional conditions for successful record lowering. The account keeps predicate routing, record-construction success, record-spread effects, block sequencing, and any omitted mixed spread separate.

## Proposed boundary for user decision

The recommended approval is a new narrow addendum that:

1. Adds brace bodies to `if`, `elsif`, and `else` while retaining the existing colon-inline and colon-indented forms byte-for-byte.
2. Gives arm braces a dedicated expression-list CST owner directly under the owning `IfArm` / `ElseArm`. It does not route through or rename ordinary `BracedStatementBlockExpression`.
3. Preserves Yulang2 source-order and arm-continuation behavior, including matching-close ownership, nested `if` association, and the containing arm's lexical scope.
4. Reuses the existing conditional HIR/inference/runtime `If` carrier only after the body interpretation is explicitly established. Conditions and every ordinary expression item retain their source occurrence/range; branch order and effects remain in the existing conditional owner.
5. Leaves empty, record-shaped, record-spread, non-record sequence, and mixed-spread Yulang3 behavior undecided until their exact Y2 dispatch and the desired compatibility boundary are reviewed. It leaves Yulang3 implementation authority gated until those source-to-consumer obligations are accepted.

The proposal leaves several related decisions open for the user. Yulang2 distinguishes record-shaped groups (including empty and some spread cases) from groups sent to block lowering. This does not establish that Yulang3 should preserve that dispatch, nor that it should replace it with one uniform expression-list meaning. Any deliberate difference must be named. In particular, mixed non-record spread may be omitted by historical block lowering, while record spread has an actual record consumer. The choices are:

- **Narrow countdown compatibility:** approve a precise singleton-only body interpretation for the countdown's non-record shapes, while explicitly deciding how all other shapes (empty, field/record, spread and multi-item) are rejected or handled. This is not full Yulang2 brace compatibility.
- **Shape-compatible brace bodies:** specify and prove a Y3 dispatch corresponding to the audited Y2 record guard and block path, including record construction/spread and mixed non-record spread behavior. This has a broader source/HIR/test scope.

The implementation must never silently ignore a source item. It must not call empty braces unit or all brace contents expression lists without an approved rule. No other source form is removed or rewritten to make the countdown succeed.

## Required implementation and evidence after approval

A successor contract must cover these connected owners:

1. **Parser/CST:** dedicated braced-arm body kind and exact grammar; condition stop and opener ownership; `else` brace dispatch; comma, semicolon and newline behavior; nested/dangling `else`; empty body; matching and missing close; malformed condition/body; recovery that preserves outer delimiters and current colon-form CST/diagnostics.
2. **HIR/source carrier:** `Builder::conditional` accepts only the dedicated body kind in the correct arm slot; source occurrence/range and arm order are retained; the body shares the arm's enclosing scope; no ordinary statement-block, record, declaration, or visibility semantics leak in.
3. **Inference:** every condition remains boolean; all arm values and effects join through the existing conditional mechanism; a missing `else` retains current discard/unit behavior; empty, record-shaped, singleton, multi-item, record-spread and mixed-spread interpretations are fixed separately. No solver algorithm or A/B claim changes in this addendum.
4. **Execution:** `Instruction::If` and `Frame::Condition` keep their current ordered condition selection and branch execution. The source-owned body must reach the same consumer with no changed handler/effect owner.
5. **Regression and product evidence:** parser structural and recovery tests; HIR/source-link tests; focused inference for empty, singleton, multi-item, spread decision, and effectful branches; CLI execution of the unchanged full 388-byte ordinary-islands source selecting `countdown_result -> 8`; then the authorized Web/WASM smoke. Preserve all current Web smoke expectations.

Run the chain serially and stop at the first failed gate. The current R132 failure receipt remains historical evidence and is never overwritten. Passing this finite sample does not prove general inference soundness, principality, native correspondence or production readiness.

## Proof and open claims

The conditional proof note and implementation handoff are separate. Their intended theorem is conditional on the approved grammar and the dedicated owner constructing exactly the retained condition/body items. They do not prove parser completeness for every accepted input, recovery correctness, source/native correspondence, candidate-admission soundness, effect hygiene, or the original Simple-sub/evaluator A/B claims.

R64/R65 and all parent inference/evaluator, source/native and production gates remain OPEN. This addendum must not reclassify or weaken any of them.

## Approval record

No approval is recorded. Status remains Draft until fresh independent review is clean. If approved, record the exact approved revision and the user's decision, then supersede only the colon-only `if` grammar boundary and the brace-body deferral stated in the architecture. A separate implementation contract is still required.
