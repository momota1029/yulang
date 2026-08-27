# ASOB integration matrix

## 1. Purpose and scope

This appendix is the gate-by-gate companion to [Ambient statement-owner boundary](ambient-statement-owner-boundary.md). It records the complete 19-gate implementation ledger and judge-point families. The main page remains the authority for `ASOB-G`, `ASOB-P`, `ASOB-R`, semantics, and residual definitions.

## 2. Judge-point enumeration

| grammar family / continuation gap | ASOB gate |
| --- | --- |
| root, indented, With-inline, Mod-inline scope lifetime; braced barriers; If companion identity | 1–6 |
| OperatorChain LED, fixed tail, ML argument, terminal tail | 7 |
| ParenthesizedExpression, Call, Index, Projection tuple/record list, separator/retry/close | 8, 16–17 |
| Pattern LED/annotation and Parenthesized/List/Record Pattern | 9, 16–17 |
| Struct named-brace/tuple field lists and RHS TypeExpression | 10, 16–17 |
| NamedRecord normal/recovery/field-colon/RHS | 11, 16–17 |
| Type path/call/apply/arrow/malformed continuation and shared type-delimited Call/group/EffectRow/BracketRow | 12, 16–17 |
| PolymorphicVariant `NT-1..8` and `IT-1..4` | 13 |
| BracketRow `BR-N`, `BR-L`, `BR-R`, `BR-RP1..4`, `BR-H`, `BR-A` | 14 |
| Forall bounded phases and colon-inline outer-owner query | 15 |
| four residual families | 18 |
| depth-2+ cross-construct restoration and final public regression | 19 |

## 3. Gate-by-gate ledger

| gate | design-doc lines | implementation | commit(s) | primary file(s) | representative fixture |
| --- | --- | --- | --- | --- | --- |
| 1 | 19112–19113 | rollback-owned ambient/If state, allocator, checkpoint, accessors | `723760c1` | `session.rs` | not independently fixture-tagged |
| 2 | 19114–19116 | sink-free ambient and companion predicates | `723760c1` | `session.rs` | `if_continuation_owner_keeps_identity_visibility_and_probe_rollback_exact` |
| 3 | 19117–19118 | baseline/barrier lookup and root/indented/With/Mod scope wiring | `5cafd19a` | `session.rs`, `expression.rs`, `declaration.rs` | `root_ambient_scope_is_balanced_after_normal_and_recovery_root_loops`, `mod_inline_ambient_scope_is_balanced_after_ast_and_direct_bodies` |
| 4 | 19119–19120 | braced barrier, outer-companion suspension, inner visibility | `a9e6078c` | `session.rs`, `expression.rs` | not independently fixture-tagged |
| 5 | 19121–19123 | complete If-chain identity-frame lifetime | `876d11de` | `session.rs`, `expression.rs` | `if_continuation_owner_keeps_identity_visibility_and_probe_rollback_exact` |
| 6 | 19124–19125 | one exact companion-spelling primitive | `cce368b5` | `session.rs`, `expression.rs` | not independently fixture-tagged |
| 7 | 19126–19127 | OperatorChain dynamic/fixed/ML/terminal pre-commit checks | `af3cce2f` | `expression.rs` | `operator_chain_returns_an_ambient_if_companion_gap_without_continuing` |
| 8 | 19128–19129 | expression-delimited lists, retry, and close recovery | `a355058d` | `expression.rs` | `call_tail_preserves_ambient_if_companions_for_inline_body_and_condition`, `expression_delimited_tails_return_ambient_if_companions_to_their_owner` |
| 9 | 19130–19131 | Pattern LED/annotation and delimited Pattern integration | `f38c77d8` | `pattern.rs` | not independently fixture-tagged |
| 10 | 19132–19133 | Struct named-brace/tuple lists and field RHS integration | `d58f6dd0` | `declaration.rs` | `struct_lists_leave_ambient_if_companions_for_the_statement_owner` |
| 11 | 19134–19135 | NamedRecord loops and field recovery/positional-fence composition | `b906428f` | `type_expr.rs` | not independently fixture-tagged |
| 12 | 19136–19138 | TypeExpression tails and shared type-delimited driver | `da4a6fbe`, `52e1853b` | `type_expr.rs` | not independently fixture-tagged |
| 13 | 19139–19141 | PolymorphicVariant tag/payload judges and safe scanners | `45c198b0` | `type_expr/polymorphic_variant.rs` | not independently fixture-tagged |
| 14 | 19142–19143 | BracketRow continuation and mandatory head/arrow judges | `5f627f1c` | `type_expr.rs` | not independently fixture-tagged |
| 15 | 19144–19146 | Forall phases and colon-inline outer-owner query | `f8b95909` | `type_expr.rs`, `expression.rs` | not independently fixture-tagged |
| 16 | 19147–19149 | original-gap implicit-list ordering and one next-slot opening | no dedicated gate-tagged commit — this cross-construct invariant is established as each construct gate (7–15, 18) wires the predicate before its own local boundary commit; `5f627f1c`'s own message reports gates 1–13/15–18 unregressed rather than claiming 16/17/19 | `expression.rs`, `pattern.rs`, `type_expr.rs`, `declaration.rs` | `malformed_delimited_item_retry_stops_before_an_ambient_if_companion` (introduced by Gate 8's `a355058d`, confirmed via `git log -S`) |
| 17 | 19150–19151 | recovery-cardinality matrix | no dedicated gate-tagged commit — satisfied cumulatively by each construct gate's (7–15, 18) own recovery-cardinality fixtures; `5f627f1c` touches only `type_expr.rs` (BracketRow) per its diffstat and does not implement this generic matrix | `expression.rs`, `pattern.rs`, `type_expr.rs`, `declaration.rs` | not independently fixture-tagged |
| 18 | 19152–19154 | four known-residual characterization fixtures | `aa7e1cbd` | `expression.rs` | `asob_known_residual_same_indent_statement_is_still_taken_by_struct_recovery`, `asob_known_residual_braced_current_depth_and_companion_suspension_remain_distinct`, `asob_known_residual_case_and_catch_arm_newlines_can_be_taken_by_call_recovery` |
| 19 | 19155–19157 | depth-2+ restoration and final regression | no dedicated gate-tagged commit — the restoration invariant this gate describes was already exercised by Gate 3's scope-wiring fixture | `session.rs`, `expression.rs`, `declaration.rs`, `pattern.rs`, `type_expr.rs` | `indented_and_with_inline_ambient_scopes_restore_after_ast_and_direct_episodes` (introduced by Gate 3's `5cafd19a`, confirmed via `git log -S`) |

`7b5ab178` finalized the design as Authoritative and is not an implementation gate. All listed fixture names are source tests; “not independently fixture-tagged” intentionally avoids asserting a gate-specific test where source naming does not establish one.

## 4. Consumer-page cross-reference

Concrete grammar contracts are documented in [braced statement block](../expressions/braced-statement-block.md), [case/catch](../expressions/case-catch.md), [call/field/path tails](../expressions/call-field-path-tails.md), [if expression](../expressions/if-expression.md), [Pattern core](../patterns/pattern-core.md), [list pattern](../patterns/list-pattern.md), [record pattern](../patterns/record-pattern.md), [type annotation](../patterns/type-annotation.md), [TypeExpression core](../types/type-expression-core.md), [NamedRecord type](../types/named-record-type.md), [polymorphic-variant type](../types/polymorphic-variant-type.md), [BracketRow grammar](../types/bracket-row-grammar.md), [equality type](../statements/equality-type.md), [bare nominal type](../statements/bare-nominal-type.md), [derives attachment](../statements/derives-attachment.md), and [cast declaration](../statements/cast-declaration.md).
