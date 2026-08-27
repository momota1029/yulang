# ASOB integration matrix

## 1. 目的と範囲

この appendix は [Ambient statement-owner boundary](ambient-statement-owner-boundary.md) の gate-by-gate companion。complete 19-gate implementation ledger と judge-point family を記録する。`ASOB-G`、`ASOB-P`、`ASOB-R`、semantics、residual definition の正本は main page のまま。

## 2. judge-point enumeration

| grammar family / continuation gap | ASOB gate |
| --- | --- |
| root、indented、With-inline、Mod-inline scope lifetime、braced barrier、If companion identity | 1–6 |
| OperatorChain LED、fixed tail、ML argument、terminal tail | 7 |
| ParenthesizedExpression、Call、Index、Projection tuple/record list、separator/retry/close | 8、16–17 |
| Pattern LED/annotation と Parenthesized/List/Record Pattern | 9、16–17 |
| Struct named-brace/tuple field list と RHS TypeExpression | 10、16–17 |
| NamedRecord normal/recovery/field-colon/RHS | 11、16–17 |
| Type path/call/apply/arrow/malformed continuation と shared type-delimited Call/group/EffectRow/BracketRow | 12、16–17 |
| PolymorphicVariant `NT-1..8` と `IT-1..4` | 13 |
| BracketRow `BR-N`、`BR-L`、`BR-R`、`BR-RP1..4`、`BR-H`、`BR-A` | 14 |
| Forall bounded phase と colon-inline outer-owner query | 15 |
| four residual family | 18 |
| depth-2+ cross-construct restoration と final public regression | 19 |

## 3. gate-by-gate ledger

| gate | design-doc lines | implementation | commit(s) | primary file(s) | representative fixture |
| --- | --- | --- | --- | --- | --- |
| 1 | 19112–19113 | rollback-owned ambient/If state、allocator、checkpoint、accessor | `723760c1` | `session.rs` | not independently fixture-tagged |
| 2 | 19114–19116 | sink-free ambient/companion predicate | `723760c1` | `session.rs` | `if_continuation_owner_keeps_identity_visibility_and_probe_rollback_exact` |
| 3 | 19117–19118 | baseline/barrier lookup と root/indented/With/Mod scope wiring | `5cafd19a` | `session.rs`、`expression.rs`、`declaration.rs` | `root_ambient_scope_is_balanced_after_normal_and_recovery_root_loops`、`mod_inline_ambient_scope_is_balanced_after_ast_and_direct_bodies` |
| 4 | 19119–19120 | braced barrier、outer-companion suspension、inner visibility | `a9e6078c` | `session.rs`、`expression.rs` | not independently fixture-tagged |
| 5 | 19121–19123 | complete If-chain identity-frame lifetime | `876d11de` | `session.rs`、`expression.rs` | `if_continuation_owner_keeps_identity_visibility_and_probe_rollback_exact` |
| 6 | 19124–19125 | one exact companion-spelling primitive | `cce368b5` | `session.rs`、`expression.rs` | not independently fixture-tagged |
| 7 | 19126–19127 | OperatorChain dynamic/fixed/ML/terminal pre-commit check | `af3cce2f` | `expression.rs` | `operator_chain_returns_an_ambient_if_companion_gap_without_continuing` |
| 8 | 19128–19129 | expression-delimited list、retry、close recovery | `a355058d` | `expression.rs` | `call_tail_preserves_ambient_if_companions_for_inline_body_and_condition`、`expression_delimited_tails_return_ambient_if_companions_to_their_owner` |
| 9 | 19130–19131 | Pattern LED/annotation と delimited Pattern integration | `f38c77d8` | `pattern.rs` | not independently fixture-tagged |
| 10 | 19132–19133 | Struct named-brace/tuple list と field RHS integration | `d58f6dd0` | `declaration.rs` | `struct_lists_leave_ambient_if_companions_for_the_statement_owner` |
| 11 | 19134–19135 | NamedRecord loop と field recovery/positional-fence composition | `b906428f` | `type_expr.rs` | not independently fixture-tagged |
| 12 | 19136–19138 | TypeExpression tail と shared type-delimited driver | `da4a6fbe`、`52e1853b` | `type_expr.rs` | not independently fixture-tagged |
| 13 | 19139–19141 | PolymorphicVariant tag/payload judge と safe scanner | `45c198b0` | `type_expr/polymorphic_variant.rs` | not independently fixture-tagged |
| 14 | 19142–19143 | BracketRow continuation と mandatory head/arrow judge | `5f627f1c` | `type_expr.rs` | not independently fixture-tagged |
| 15 | 19144–19146 | Forall phase と colon-inline outer-owner query | `f8b95909` | `type_expr.rs`、`expression.rs` | not independently fixture-tagged |
| 16 | 19147–19149 | original-gap implicit-list ordering と one next-slot opening | 専用のgate-tagged commitなし——この cross-construct invariant は各 construct gate(7–15、18)が own local boundary commit 前に predicate を wire することで成立する。`5f627f1c` 自身の message は gate 1–13/15–18 の unregressed を報告するだけで 16/17/19 を実装したとは主張していない | `expression.rs`、`pattern.rs`、`type_expr.rs`、`declaration.rs` | `malformed_delimited_item_retry_stops_before_an_ambient_if_companion`(Gate 8 の `a355058d` で導入、`git log -S` で確認) |
| 17 | 19150–19151 | recovery-cardinality matrix | 専用のgate-tagged commitなし——各 construct gate(7–15、18)own recovery-cardinality fixture が累積的に満たす。`5f627f1c` は diffstat 上 `type_expr.rs`(BracketRow)のみに触れ、この generic matrix を実装しない | `expression.rs`、`pattern.rs`、`type_expr.rs`、`declaration.rs` | not independently fixture-tagged |
| 18 | 19152–19154 | four known-residual characterization fixture | `aa7e1cbd` | `expression.rs` | `asob_known_residual_same_indent_statement_is_still_taken_by_struct_recovery`、`asob_known_residual_braced_current_depth_and_companion_suspension_remain_distinct`、`asob_known_residual_case_and_catch_arm_newlines_can_be_taken_by_call_recovery` |
| 19 | 19155–19157 | depth-2+ restoration と final regression | 専用のgate-tagged commitなし——この gate が記述する restoration invariant は Gate 3 の scope-wiring fixture で既に exercise 済み | `session.rs`、`expression.rs`、`declaration.rs`、`pattern.rs`、`type_expr.rs` | `indented_and_with_inline_ambient_scopes_restore_after_ast_and_direct_episodes`(Gate 3 の `5cafd19a` で導入、`git log -S` で確認) |

`7b5ab178` は design を Authoritative に finalization した commit で implementation gate ではない。listed fixture は source test。not independently fixture-tagged は source naming で gate-specific test を確定できない箇所を意図的に示す。

## 4. consumer-page cross-reference

concrete grammar contract は [braced statement block](../expressions/braced-statement-block.md)、[case/catch](../expressions/case-catch.md)、[call/field/path tail](../expressions/call-field-path-tails.md)、[if expression](../expressions/if-expression.md)、[Pattern core](../patterns/pattern-core.md)、[list pattern](../patterns/list-pattern.md)、[record pattern](../patterns/record-pattern.md)、[type annotation](../patterns/type-annotation.md)、[TypeExpression core](../types/type-expression-core.md)、[NamedRecord type](../types/named-record-type.md)、[polymorphic-variant type](../types/polymorphic-variant-type.md)、[BracketRow grammar](../types/bracket-row-grammar.md)、[equality type](../statements/equality-type.md)、[bare nominal type](../statements/bare-nominal-type.md)、[derives attachment](../statements/derives-attachment.md)、[cast declaration](../statements/cast-declaration.md) にある。
