# R135 rev4: Y2 brace-shape consumer audit

Status: **SOURCE-ATTRIBUTED CANDIDATE AUDIT; NOT INDEPENDENTLY REVIEWED.**
Author: `/root/r135_braced_if_proof`; audit revision 2.
Authority: R135 rev5, SHA-256 `6f263805f1cf81c436caaa96ad87889f7e1c0d25a46d5a957cafed1ea0b969de`, supplied by Luna before this sequential revision. Existing followup identity is permitted by Luna; no fresh-session claim. Session UUID/model/effort are UNKNOWN.

## Parent application and correction

The parent still asks for dedicated braced conditional expression-list CST through Y3 LocalSource and existing If consumers, preserving syntax ownership, arm order, source keys, lexical scope, values/effects and recovery over the original source domain. No syntax or semantic adoption is authorized.

This audit corrects two overbroad source statements in the frozen earlier note. Y2 empty braces need not take the block/unit path: the record predicate distinguishes genuinely empty child lists from separator-only groups. Spread lowering also depends on the record-versus-block route. Y3 a brace immediately after bare `else` produces an inline Missing product and is handed back unconsumed; it is not accepted as an ordinary braced body.

The earlier singleton lemma remains conditional only. Its application must establish the actual brace shape and consumer route; one parsed Expr item is insufficient to distinguish a field/record shape from an ordinary expression body. Its source construction, HIR recognition, recovery, provenance and inference premises remain unproved. No parent theorem, Y3 native correspondence or production gate is closed.

## Evidence provenance and pins

This author ran no commands during this audit. Luna supplied inspected excerpts and confirmed their exact rev4 source pins; rev5 supplies the complete predicate and multiple-spread correction without changing those source dependencies. The author classifies those supplied predicates and branches; this is not independent source inspection or review. Historical source authors are UNKNOWN.

All Y2 paths are rooted at `/home/momota1029/rust/yulang2-oracle-capture`.

| Owner | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/chain.rs` | `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6` |
| `crates/infer/src/lowering/expr_syntax.rs` | `3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085` |
| `crates/infer/src/lowering/record_lit.rs` | `88ce8e06f83884fd825402565c52ab1f19e8b9932500036eae495d392a5c990c` |
| `crates/infer/src/lowering/control.rs` | `4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963` |
| `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `crates/parser/src/expr/control.rs` | `0102f9e8c6ded9c03c51a71356a1532a9db8742de181d649f642ad9d325f4e5b` |
| `crates/parser/src/expr/group.rs` | `bb58bd49ec272003e69d4675c2d6ee1de470e3c1ebaed0f632b6f117629acf38` |

Y3 correction owner: `crates/yu-syntax/src/expression/if_expr.rs`, SHA-256 `509af68c34e11a2a2d5538df8bab84c599d68154a3f03d57c304bbfb04d8cd39`.

Prior frozen candidate: `notes/theory/2026-10-20-braced-if-elaboration.md`, SHA-256 `918e78e804f019752f816b32c4ba01f35673fef128c2c4493b7202271848e942`. It is not edited; this audit supersedes only the erroneous source descriptions identified above.

## Predicate and consumer derivation

The supplied `brace_group_is_record_literal` excerpt in `expr_syntax.rs:115` walks children. Each Expr must be an inline-record field, otherwise it returns false. An ExprSpread must contain an Expr child, otherwise it returns false. Separator children are allowed. Every other child kind, including Missing and Error, returns false. After these checks the final result is `has_item || !saw_child`. This classifies the supplied child sequence only: it does not establish parser reachability, successful lowering or recovery behavior.

The supplied `chain.rs:590` dispatch first selects `lower_record_literal` for a BraceGroup satisfying that predicate; the later `IndentBlock | BraceGroup` branch selects `lower_expr_block`. Therefore the block path is a fallback, not the semantics of all brace groups.

The supplied `record_lit.rs:55` consumer constructs `RecordSpread::{Head,Tail}` / `Pos::Record*` forms and, on successful field/operand lowering, accumulates their effects. Predicate acceptance permits multiple ExprSpread children when each contains an Expr operand. The record lowerer nevertheless rejects a second spread before lowering that second operand. Successful record lowering therefore requires at most one spread, valid fields and successful operand lowering. This audit makes no claim about the first operand's lowering state when a later spread is rejected. With zero items the record path constructs `Pos::Record([])` and `Expr::Record`. Neither runtime behavior nor a Y3 semantic rule follows.

| Observed child shape | Predicate result and route | Consumer consequence supported by supplied evidence |
| --- | --- | --- |
| Genuinely empty: no children observed | `!saw_child` true; record route | Empty record construction, not the block lowerer's unit result. |
| One or more inline-record-field Expr items, optional separators, with no disqualifying Expr/spread | `has_item` true; record route | Field/record lowering. A singleton field is not an ordinary singleton expression block. |
| Spread-only, each ExprSpread containing an Expr operand | `has_item` true; record route, including multiple such spreads | Successful lowering can contain at most one spread and requires valid operand lowering. A second spread is rejected before its operand is lowered; no claim about the first operand's lowering state. |
| Ordinary singleton non-field Expr | Returns false at that Expr; block route | `block_lowering_items` retains the Expr; reported block lowering uses it as tail expression. |
| Multiple items including at least one non-field Expr | Returns false; block route | Selected `Binding | Expr | ForStmt` items follow block lowering. Exact preceding/tail cases remain case-dependent. |
| Mixed ordinary non-field Expr plus ExprSpread | False due to non-field Expr; block route | The reported block-item filter omits ExprSpread. Omission concern is confined to this non-record route. Full source reachability/effect consequence is not proved here. |
| Separator-only: children observed, no qualifying item | `has_item = false`, `saw_child = true`; false, block route | Predicate distinguishes this from genuine emptiness. Exact lowerer result/diagnostic for this malformed or degenerate shape is not established by the predicate alone. |
| Expr that is not an inline-record field; or ExprSpread lacking an Expr child | False by explicit rejection | Falls through to block dispatch; successful lowering, error behavior and parser reachability do not follow. |
| Any other child kind, including Missing or Error | False by the complete predicate | Block fallback dispatch follows for this hypothetical group; parser reachability, lowering outcome, diagnostics and recovery ownership remain separate obligations. |

These rows classify supplied shapes, not an exhaustive theorem of accepted surface programs. In particular the predicate does not prove that a separator-only or malformed CST is emitted by the real parser. The historical parser's comma/semicolon and spread acceptance alone does not establish every recovery shape.

Y2 `lower_if_arm_body` invokes expression lowering. Thus the route above matters inside conditional arms as well. The reported `lower_if` value/effect joins do not repair a missing item in its body lowerer and do not establish Y3 inference correspondence.

## Correct Y3 bare-else boundary

Luna supplied `if_expr.rs:499`: when the inline helper encounters a boundary it invokes `emit_inline_missing` and completes using `handoff(item)`. The supplied boundary predicate at `if_expr.rs:597` includes `LBrace`. Consequently the path after a bare else with a brace produces Missing and returns the brace unconsumed. The earlier note's claim that this brace is accepted via the ordinary expression route is withdrawn.

The proposed dedicated ElseArm body constructor must therefore discharge its own acceptance and recovery obligations. Neither existing Missing recovery nor an ordinary statement-block route proves that constructor exists. This correction leaves current colon behavior and all parser/HIR/runtime sources untouched.

## Remaining premises and exact next step

1. Independently verify these pinned excerpts and the complete predicate. Its result on unexpected/Missing/Error children is now specified as false; actual parser production of empty/separator-only/malformed child sequences and their lowering/recovery outcomes remain unproved.
2. Trace the exact unchanged countdown CST through this record predicate before using the conditional singleton lemma. Do not infer its route from item count alone.
3. Establish full non-record mixed-spread source reachability and actual lowering/diagnostic/effect consequences before presenting a source-qualified counterexample. Owners: `ExprListMachine`, `brace_group_is_record_literal`, `lower_expr_block`, `block_lowering_items` and `lower_block_items`.
4. Return Y3 empty/field/record/spread/sequence value/effect choices to Luna's authority process. This audit supplies historical evidence and chooses none of them.
5. Actual dedicated Y3 IfArm/ElseArm constructors, LocalSource body recognizers, source-key/lexical/recovery preservation and all-arm inference remain missing. Preserve ordinary Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying intrusion and generalization. No inference bypass or identity collapse is proposed.

## Revision history and correction receipts

Rev4 audit r1 SHA-256: `43c871fa2865539c6243416299ba3aeb7edeee038870f688e9e6c5344baba86e`; rev4 handoff r1 SHA-256: `5730ba160f1abc22c0d83f7e4fbe516f2aed2a7859372801cf5e50f29d53ee46`. Rev4 contract SHA-256: `971fc2692374ef3feadf344a3a4e6fa6d936c9da838879f3f2b78c6e7803143a`.

Luna's rev5 followup supplies two correction findings: all non-Expr/non-ExprSpread/non-Separator child kinds fail the predicate; and multiple qualifying spreads can pass that predicate although the record lowerer rejects the second before lowering its operand. This revision records those findings without claiming a fresh reviewer receipt, first-operand lowering state, runtime result or semantic adoption. No independent review receipt identifier was supplied: UNKNOWN. The earlier bare-else and empty-record corrections remain in force.

Next in scope is Luna intake and fresh independent review of this frozen audit together with the prior conditional lemma. No descendant or implementation activity is authorized here. All new paths are this note and `tasks/agent-loop/inbox/20261020-r135-proof-audit.md`; scratch paths NONE. **STOP / NO_DESCENDANTS.**
