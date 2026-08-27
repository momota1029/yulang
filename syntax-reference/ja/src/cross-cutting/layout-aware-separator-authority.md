# layout-aware comma-or-newline 区切り列の authority

## 1. 状態・正本・改訂台帳

正本は [parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md) の layout-aware separator addendum、9314–9693 行。冒頭 status は final sign-off より前のままだが、9692–9693 行の closing signature は著者査読とユーザ承認を記録している。ParenthesizedExpression (4099–4351)、ColonApplication (5014–5467)、Pattern core / ParenthesizedPattern (6629–7242)、ListPattern (8019–8612)、RecordPattern (8613–9312) の separator 部分を改訂する。implementation authority は `8ffd405f` と `81ef211d`。

## 2. 問題・対象範囲・非対象

この mechanism は complete item 間の maximal trivia が delimiter-local comma-or-newline boundary か、current item の continuation trivia かを決める。parenthesized expression list、parenthesized/list/record pattern、call/index/projection item、delimited type item、polymorphic-variant row、struct field sequence が対象。semicolon の共通 separator 化、generic `Separator` node、item grammar の変更、statement/arm ownership の裁定は非対象。

## 3. canonical rule と decision procedure

```text
DelimitedSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(base_indent)
ImplicitNewlineBoundary(base_indent) :=
    maximal trivia run containing a physical newline
    whose following-line indentation <= base_indent
```

`base_indent` は opener trivia 後に一度 capture する。physical newline を含み incoming baseline より深いときだけ following indent を使い、それ以外は incoming baseline。item 後は current-depth comma、qualifying newline、deeper newline、comma なし same-line candidate への zero-width missing separator と same-position retry の順で裁定する。comma-plus-newline と newline-plus-comma は各々一つの boundary cluster。

## 4. authority・precedence・ownership transfer

local owner が comma または qualifying newline を accept できるのは local item complete 後で active outer owner が予約していないときだけ。literal comma は consume する。implicit newline に synthetic CST token はなく raw trivia は direct-CST container に残る。deeper newline は item に残る。caller-owned punctuation/close は untouched で返し、local missing separator は同じ byte から retry する。

## 5. worked trace と byte ownership

正本は source classification を示すだけで byte-range CST tree はないため、ここでも range を作らない。

| source と design-doc 行 | decision と ownership |
| --- | --- |
| `()` (9522) | valid empty parenthesized list |
| `(a,)` (9524) | literal trailing comma。one-tuple semantics は literal-comma semantics のまま |
| `(\n  a\n  b\n)` (9525) | base 2。two items。final implicit boundary は valid で empty item を作らない |
| `(a\nb)` at base 0 (9526) | qualifying newline。two items、`Missing(Comma)` なし |
| `(a\n  b)` at base 0 (9527) | deeper trivia は first `OperatorChain` に残り、`b` は second item でない |

同じ revision は `[]`、`[a,]`、`[a\nb]` に及ぶ（9573–9578 行）。in-place RecordPattern revision は 9630 行で `{a\nb}` を復元する。

## 6. participating parser state と adoption matrix

| state/type | producer | query / consumer | observable effect |
| --- | --- | --- | --- |
| `LayoutDelimitedFrame` | `LayoutDelimitedFrame::after_opening_trivia` / `LayoutDelimitedFrame::inline` | `LayoutDelimitedFrame::boundary_after_trivia` | captured base のみ。AST node なし |
| `LayoutDelimitedBoundary` | frame query | item/separator driver | `ImplicitNewline`、`DeeperNewline`、`None`。synthetic separator なし |
| `IndentationBaseline` | ParseLocal indentation scope | frame construction | incoming indentation identity |
| `StopSet` と `StopKind` | caller grammar frame | local/outer boundary check | caller stop を保存 |
| `Delimiter` | delimiter stack | close judge | local/outer close ownership を区別 |

adopter は各 grammar file で `push_layout_delimited_baseline` / `pop_layout_delimited_baseline`、`push_pattern_layout_baseline` / `pop_pattern_layout_baseline`、`push_layout` / `pop_layout`、`push_struct_layout` / `pop_struct_layout` を使う。

## 7. recovery・cardinality・no-cascade contract

item 間または close 前の qualifying newline は valid で Missing/Error を emit しない。deeper newline は item に残す。comma なし same-line next item は一つの zero-width missing separator と retry。repeated comma と semicolon は construct-specific recovery を保ち、semicolon は invalid のまま。direct CST は source token/raw trivia だけを記録し、source-absent separator を作らず、一原因を second separator error へ cascade させない。

## 8. lifecycle・rollback・invariant

frame は opener/inline entry で capture/push し、normal/recovery/rollback の全 exit で pop。後続 content、error range、EOF から base を再計算しない。nested owner は caller 再開前に outer frame を restore し、AST/direct は同じ decision を行う。

## 9. Yulang2 divergence

equal-or-shallower physical newline は trailing implicit boundary を含む first-class implicit separator。literal comma は fabricate せず、既存 literal trailing-comma AST semantics は変わらない。

## 10. known residual・exclusion・extension rule

ambient statement/arm owner または caller stop がすでに own する boundary はこの mechanism が決めない。その layer は ASOB が記述する。future delimited construct は item grammar、frame/base capture、close/stop ownership、trailing separator rule を宣言し、private raw-newline rescan ではなくこの query を reuse する。

## 11. 実装・fixture・consumer page cross-reference

core implementation は `LayoutDelimitedFrame`、`LayoutDelimitedBoundary`、`LayoutDelimitedFrame::after_opening_trivia`、`LayoutDelimitedFrame::boundary_after_trivia`。fixture は `parenthesized_layout_boundaries_preserve_ast_direct_shape_and_trivia`、`parenthesized_patterns_accept_comma_or_layout_newline_boundaries`、`list_patterns_accept_comma_or_layout_newline_and_keep_spread_items`、`type_groups_reuse_layout_boundaries_without_synthetic_separator_nodes`、`named_record_types_are_primary_fields_with_comma_or_newline_boundaries`、`struct_named_brace_fields_keep_their_own_layout_and_type_apply_boundary`。

consumer summary は [parenthesized expression](../expressions/parenthesized-expression.md)、[colon application](../expressions/colon-application.md)、[call/field/path tail](../expressions/call-field-path-tails.md)、[index/projection tail](../expressions/index-projection-tails.md)、[Pattern core](../patterns/pattern-core.md)、[list pattern](../patterns/list-pattern.md)、[record pattern](../patterns/record-pattern.md)。
