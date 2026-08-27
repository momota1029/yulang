# Ambient statement-owner boundary (ASOB)

## 1. 状態・正本・改訂台帳

正本の ASOB addendum は [parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md) の 18358–19160 行で、`7b5ab178` が finalization を行った。canonical section は ambient stack / identity / barrier / predicate の `ASOB-G`、precedence の `ASOB-P`、recovery ownership/cardinality の `ASOB-R`。implementation は `723760c1` から `5f627f1c` の 19 gate にまたがる。完全な gate/commit ledger は後続の [ASOB integration matrix](asob-integration-matrix.md) に置く。

## 2. 問題・対象範囲・非対象

ASOB は statement context 内の nested delimited/layout owner が missing close を持つときの二つの collision class を閉じる。nearest visible statement baseline より strictly shallow な physical newline と、exact `else` / `elsif` を持つ active `IfExpression` companion。これらの exact case では local item/list continuation が gap を consume する前に ambient owner が勝つ。

Struct field、NamedRecordType、type-delimited form、polymorphic variant、BracketRow、expression-delimited tail、Pattern-delimited form、Forall、colon-inline argument の continuation/recovery authority を amend する。item grammar、layout base、explicit separator、matching-close recognition、AST/CST shape、recovery role、diagnostic、ordinary same-indent Statement collision、Case/Catch arm authority、non-If contextual stop は変えない。

## 3. canonical rule と decision procedure

`ASOB-G` は rollback-owned ambient-owner stack と If-companion stack を持つ。braced barrier は visible-baseline lookup を停止し、barrier 前 If frame を隠す。inline canonical-statement frame は baseline lookup に transparent。

```text
AnyAmbientOwnerClaims(gap) :=
    StrictDedentFromNearestVisibleStatementBaseline(gap)
    or IfContinuationOwner(gap).is_some()

AmbientPreCommitJudge(gap, local_candidate) :=
    if AnyAmbientOwnerClaims(gap)
    then CallerOwnedBoundary
    else EvaluateExistingLocalCandidate(local_candidate)
```

strict dedent は physical newline と nearest visible root/indented baseline より strictly shallow な following indent を要求する。`IfContinuationOwner` は exact `else` / `elsif` と frame base を満たす first visible companion identity を返す。sink-free query は maximal trivia run と following maximal word を probe し、input / line / local / sink を rollback する。

## 4. authority・precedence・ownership transfer

`ASOB-P` の順序は actual local matching close/fixed caller stop、locally allowed explicit separator、completed/recovered continuation gap の ambient claim、最後に既存 local continuation/layout/retry。literal separator は authority を保ち exactly one next slot を開く。それ以外の ambient claim は original gap を non-consume で返し local slot を開かない。

bare implicit boundary では ambient/local layout predicate が original unconsumed gap を見る。ambient false かつ local success のときだけ consume して `AfterOwnerSafeImplicitBoundary` に入り、post-newline re-probe は禁止。If arm は `IfContinuationOwner` が own identity を返したときだけ companion を consume する。

## 5. worked trace と byte ownership

| source と design-doc 行 | ASOB decision | required result |
| --- | --- | --- |
| `if condition:\n  struct S { x: Int\nelse: 0` (18761–18763) | strict dedent と own `else` companion が original newline を claim | Struct は missing `}` 一つ、missing field なし。newline と `else: 0` は If-owned |
| `if condition: f(x else: 0` (18775) | inline companion が ML continuation 前に visible | Call は missing `)` 一つ、missing argument なし。`else: 0` は ElseArm |
| `if condition:\n  { else: 0 }\nelse: 1` (18808–18810) | braced barrier が brace 内で outer companion を suspend し、後で resume | inner `else` は local、outer `else: 1` は companion |
| `if condition:\n  my [x\nelse: 0` (18833–18835) | ListPattern は local implicit boundary を commit できない | missing `]` 一つ、missing pattern item zero、companion は outer-owned |
| `struct S { x: Int,` (18709–18711) | explicit comma が terminal recovery より前に local authority | existing missing field 一つと distinct missing `}` 一つを保つ |

これは source/recovery trace。ASOB は単一の byte-range CST tree を定義せず、participating owner ごとの source trivia/recovery ownership を保つ。

## 6. participating parser state と adoption matrix

| state/type | producer | query / consumer | phase | observable effect |
| --- | --- | --- | --- | --- |
| `AmbientOwnerScopeFrame` | root/indented/braced/With/Mod scope wiring | baseline/barrier lookup | statement context lifetime | scope kind、baseline、visibility floor を保持 |
| `AmbientOwnerScopeKind` | `AmbientOwnerScopeFrame` constructor | nearest-visible-baseline walk | root/indented/barrier/inline distinction | barrier が outer baseline visibility を停止 |
| `BracedBarrierOrigin` | braced statement block/Catch braced arm entry | barrier identity | brace lifetime | pre-barrier companion frame を suspend |
| `InlineStatementOwnerKind` | With/Mod inline entry | transparent inline scope | exactly-one Statement episode | baseline を作らず origin を保持 |
| `IfExpressionCompanionFrame` | `push_if_expression_companion` | `if_continuation_owner` | complete If chain | immutable base、exact word、identity を capture |
| `IfExpressionCompanionId` | ParseLocal ID allocator | arm own-ID comparison | nested companion transition | inner If が outer companion を consume しない |
| `ParseLocalCheckpoint` | `ParseLocal::checkpoint` | `ParseLocal::rollback` | all speculative exit | stack depth と ID state を restore |

core query は `session.rs` の `any_ambient_owner_claims` と `if_continuation_owner`。production call site は `expression.rs`、`pattern.rs`、`type_expr.rs`、`type_expr/polymorphic_variant.rs`、`declaration.rs` に広がる。

## 7. recovery・cardinality・no-cascade contract

`ASOB-R` は recovery vocabulary/synthetic node を追加しない。ambient claim が bare implicit candidate を veto すると separator/next item/field slot は commit されない。missing item/field は zero で、accepted/unclosed delimiter instance ごとに既存 missing close が一つ。explicit または commit 済み local implicit separator 後は、既存 recovery の missing next item/field 一つと distinct missing close 一つを保つ。

caller は untouched trivia/boundary byte を受け取る。nested owner は同じ gap を independently return し各自の close slot を realize できる。これは accepted construct instance ごとの cardinality であり global deduplication ではない。AST/direct は lossless で one committed recovery record = one recovery node。

## 8. lifecycle・rollback・invariant

root/indented/braced/inline scope は exact frame を push し normal/recovery exit で pop。braced barrier は If-stack visibility floor を capture し inner frame を保ち pop 時に restore を assert。If frame は `IfKw` 直後に開始し `elsif` を越えて保持し、own `else` commit または final return でのみ pop。predicate 自体は sink-free/exact rollback。

completeness は compiler enforcement でなく documented + fixture-verified judge-point enumeration。completed/recovered anchor から local gap を commit し得る transition はすべて commit 前に predicate を call する。

## 9. Yulang2 divergence

ASOB は local field/item shape も match し得る位置で strict outer dedent と active exact If companion を explicit ambient authority にする。new surface token、grammar production、diagnostic role、semantic behavior は追加しない。

## 10. known residual・exclusion・extension rule

正本は四つの residual owner family を記録する。

1. missing inner close 後の same-indent ordinary canonical Statement。
2. braced statement-owner current-depth newline または missing braced close。
3. Case/Catch arm-sequence newline。CatchBraced current depth を含む。
4. missing nested delimiter 後の non-If contextual introducer/owner stop。arm `if`/`where`、`->`、binding `=` を含む。

これらは strict visible-statement dedent でも `else`/`elsif` companion identity でも claim されない ASOB residual。Cast page の four-condition predicate は Cast-contained Pattern/TypeExpression delimiter に対するこの最後の family の downstream specialization であり、第五 ASOB family でも closed owner table でもない。

future construct が ASOB の二 class を consume し得る completed/recovered gap を作るなら signed amendment、judge point、AST/direct fixture を同時に追加する。他の caller boundary へ ASOB を広げるには別 authority/priority design が必要。

## 11. 実装・fixture・consumer page cross-reference

19 gate は rollback-owned scope/predicate、root/indented/braced/inline/If lifetime を導入し、expression、Pattern、TypeExpression、struct、polymorphic-variant、BracketRow、Forall、colon-inline、recovery/cardinality、residual、restoration coverage へ integration する。代表 commit は `723760c1`、`af3cce2f`、`a355058d`、`5f627f1c`、`aa7e1cbd`。完全 ledger は [ASOB integration matrix](asob-integration-matrix.md) を見る。

代表 fixture は `operator_chain_returns_an_ambient_if_companion_gap_without_continuing`、`call_tail_preserves_ambient_if_companions_for_inline_body_and_condition`、`expression_delimited_tails_return_ambient_if_companions_to_their_owner`、`asob_known_residual_same_indent_statement_is_still_taken_by_struct_recovery`、`asob_known_residual_braced_current_depth_and_companion_suspension_remain_distinct`、`asob_known_residual_case_and_catch_arm_newlines_can_be_taken_by_call_recovery`、`asob_known_residual_suspended_arm_guard_if_is_still_consumed_inside_list_pattern`。

consumer summary は [braced statement block](../expressions/braced-statement-block.md)、[case/catch](../expressions/case-catch.md)、[call/field/path tail](../expressions/call-field-path-tails.md)、[if expression](../expressions/if-expression.md)、[Pattern core](../patterns/pattern-core.md)、[list pattern](../patterns/list-pattern.md)、[record pattern](../patterns/record-pattern.md)、[type annotation](../patterns/type-annotation.md)、[TypeExpression core](../types/type-expression-core.md)、[NamedRecord type](../types/named-record-type.md)、[polymorphic-variant type](../types/polymorphic-variant-type.md)、[BracketRow grammar](../types/bracket-row-grammar.md)、[equality type](../statements/equality-type.md)、[bare nominal type](../statements/bare-nominal-type.md)、[derives attachment](../statements/derives-attachment.md)、[cast declaration](../statements/cast-declaration.md)。
