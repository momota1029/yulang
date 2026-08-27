# Effect-row type

## 1. 状態・正本・最終確認

Authoritative な EffectRowType 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 13982–14525 行にある。current shared delimited recovery は 18358–19161 行の `ASOB-G` と 16557–17289 行の `TMN`/positional-fence authority で refine される。

実装 commit は `b0989159`、`608396fc`、`29c6a630`、`52e1853b`、`f8b95909`。このページは `063da888` を基準に確認した。

## 2. 対象範囲と非対象

EffectRowType は `'[]`、`'[e]`、`'['e]`、`'[a, b]`、`'[tick; 'effect]` を parser syntax として追加する。これは nonterminal TypePrimary で、item は full TypeExpression、separator は comma/semicolon/qualifying newline である。

open/closed/tail classification、effect inference、annotation lowering、polymorphic variant、bracket row、use-site wiring、HIR/lowering、diagnostics text、formatting は対象外である。

## 3. BNF 相当の grammar

```text
EffectRowType := Apostrophe AdjacentLBracket EffectRowOpeningTrivia [ TypeExpression { EffectRowDelimitedBoundary TypeExpression } [ EffectRowDelimitedBoundary ] ] RBracket
AdjacentLBracket := LBracket whose first byte is exactly Apostrophe.end
EffectRowDelimitedBoundary := CommaBoundary | SemicolonBoundary | ImplicitNewlineBoundary(effect_row_base)
```

apostrophe と `[` は adjacent でなければならない。Opening trivia は `effect_row_base` を一度 capture し、equal-or-shallower newline は item separator、deeper newline は current type item continuation になる。

## 4. Judge・priority・owner boundary

primary judge は active stop/close と canonical NUD `for` の後、normal type-name scan より前に complete adjacent compound `"'["` を probe する。従って `'[` は EffectRow candidate、`'e` は sigil identifier のまま、`' [` と `'/*c*/[e]` は EffectRow へ cut しない。

accept 後は bracket delimiter、EffectRow owner、local stop、layout frame をまとめて push する。これは terminal ではない。`'[e]::Result`、`Foo '[e]`、`'[e] -> Out` は ordinary tail judge に戻り、それぞれ path/apply/arrow になる。

## 5. Byte-exact CST の worked examples

追補には complete CST tree があるが byte-range 付き tree はない。ここでは range を作らない。

```text
'[]
```

設計文書 14176–14184 行は apostrophe/bracket token だけを持つ `TypeExpression > EffectRowType` を示す。

```text
'[e]
```

設計文書 14186 行以降は full TypeExpression item 一つを含む同じ row node を示す。`'[e]` と `'['e]` の差は item token category だけである。

```text
'[tick; 'effect]
```

surface list は設計文書 13991–13997 行に明記される。semicolon は row-tail interpretation ではなく ordinary parser separator である。

## 6. Parser 側 AST shape

`TypePrimary::EffectRow(EffectRowType)` は `apostrophe`、`open`、recovered ordered `items`、recovered `close`、`range` を持つ。source syntax だけを記録し、open row/closed row/tail variable を示す parser AST field はない。

direct CST は `SyntaxKind::EffectRowType` だけを追加する。apostrophe、bracket、separator、trivia、nested TypeExpression は synthetic item/list/tail wrapper なしの source-order child になる。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| missing compound introducer | EffectRow authority なし。ordinary primary recovery が所有 |
| empty / valid delimited row | valid item/close。recovery なし |
| leading/repeated separator | absent item ごとに typed EffectRow item Missing 一件 |
| valid apply continuation でない same-line next item | typed separator Missing 一件後 same-position item retry |
| malformed item の後に valid primary | item Error 一件後 same-slot retry |
| real `]` 前の trailing separator | valid trailing boundary。empty item なし |
| EOF/outer boundary 前の separator | distinct missing item/close slot |
| missing/mismatched `]` | EffectRow closing Missing/Error 一件。outer close は non-consuming |

row は EffectRow role を伴う shared type-delimited driver を再利用する。safe point は caller boundary、local separator、matching close、valid retry candidate を含み、typed no-cascade を保つ。

## 8. Boundary と state-restoration contract

accept は `Delimiter::Bracket`、`TypeDelimitedOwner::EffectRow`、row-local stop、layout frame を push し、全 exit で一度ずつ pop する。AST/direct は candidate/boundary/close/recovery decision を共有する。`ASOB-G`、`TMN`、positional-fence は ambient/If、indentation、type-owner、episode、caller-boundary state を保つ。

## 9. Yulang2 divergences

Yulang3 は apostrophe-bracket row、full type item、comma/semicolon/layout boundary を保つが、apostrophe-bracket adjacency を要求し、Yulang2 の `TypeEffectRow > TypeRow` wrapper や empty `Separator` node を出さない。semicolon は row-tail meaning を持たず syntax に留まり、generic `InvalidToken` recovery を typed slot に置換する。

## 10. Known residual / deferred surface

general hidden-boundary residual は `ASOB-G` が characterization し、EffectRow-specific exemption で広げない。row-tail semantics、open/closed classification、effect inference、lowering/HIR、resolver integration、diagnostics、formatting、use-site wiring は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/type_expr.rs` では `parse_effect_row_type`、`scan_effect_row_open`、`commit_direct_type_primary_head`、`drive_type_delimited`、`commit_direct_type_delimited`、`classify_type_delimited_recovery`、`scan_type_delimited_item_invalid_run`、`drive_type_close_slot` を参照する。

fixture は `effect_row_primary_is_adjacent_semantically_blind_and_composes_normally`、`effect_row_reuses_type_call_delimited_recovery_slots`、`type_delimited_close_recovery_keeps_a_mismatched_closer_local`、`type_close_slot_leaves_caller_owned_newlines_unconsumed`。
