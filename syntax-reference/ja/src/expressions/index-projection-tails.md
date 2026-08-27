# Index / projection tail

## 1. 状態・正本・最終確認

Authoritative な IndexTail/ProjectionTail fixed-tail 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 10184–10660 行にある。これは Call/Field/Path/ML 追補 9695–10182 行が future authority として残した body、adjacency、delimiter ownership、recovery を具体化する。

design / implementation series は `5f5416ea`、`8d3d22e2`、`5f067e33`、`0ea6bf5e`、`a6926e9d`、`6b39d612`、`4315dd90`、`f3c28bc5`。

## 2. 対象範囲と非対象

本ページは target-free source-order fixed postfix である adjacent IndexTail、tuple ProjectionTail、record ProjectionTail を定義する。body は general OperatorChain、layout-aware comma/semicolon/newline item list、owner-safe close recovery を持ち、record projection だけが exact `..` spread item を許す。

Field/Call/Path/ML recognition は shared adjacent-tail infrastructure に残る。semantic index/projection evaluation、record validation、spread position/multiplicity rule、target association、HIR lowering、inference、diagnostics wording、formatting は対象外である。

## 3. BNF 相当の grammar

```text
FixedPostfixTail += IndexTail | ProjectionTail

IndexTail := LBracket G* [ OperatorChain { IndexSeparator OperatorChain } [ IndexSeparator ] ] RBracket
ProjectionTail := ProjectionTupleTail | ProjectionRecordTail
ProjectionTupleTail := Dot LParen G* [ OperatorChain { ProjectionTupleSeparator OperatorChain } [ ProjectionTupleSeparator ] ] RParen
ProjectionRecordTail := Dot LBrace G* [ ProjectionRecordItem { ProjectionRecordSeparator ProjectionRecordItem } [ ProjectionRecordSeparator ] ] RBrace
ProjectionRecordItem := OperatorChain | ProjectionRecordSpreadItem
ProjectionRecordSpreadItem := DotDot G* OperatorChain

IndexSeparator := Comma | Semicolon | ImplicitNewlineBoundary(index_base)
ProjectionTupleSeparator := Comma | Semicolon | ImplicitNewlineBoundary(tuple_projection_base)
ProjectionRecordSeparator := Comma | Semicolon | ImplicitNewlineBoundary(record_projection_base)
```

Index は `[` 前の trivia を許さない。Projection は dot/opener adjacency を要し、dot 前の `ChainContinuingTrivia` は FieldTail と同じ continuation rule を使う。record projection item position だけが exact `..` の fixed spread authority を持ち、Index/tuple content では `..` は ordinary dynamic syntax のままである。

## 4. Judge・priority・owner boundary

active owner stop、outer matching close、equal-or-shallower newline、accepted dynamic spelling が structural tail より先に勝つ。leading trivia がない `[` は IndexTail、exact `.(` / `.{` は FieldTail より先に Projection を選ぶ。`a. (x)`/`a. {x}` は projection でない。fixed tail は introducer 後に cut し、own close/recovery 完了後に shared operand-complete loop へ戻る。

Index は Bracket + comma/semicolon/right-bracket stop、tuple projection は Parenthesis + comma/semicolon/right-parenthesis、record projection は Brace + comma/semicolon/right-brace を所有する。各々 `ExpressionDelimitedOwner` であるため、inner colon application は RHS 一つで container boundary を返す。qualifying ML continuation は item 内に留まり、equal-or-shallower newline は container へ返る。

## 5. Byte-exact CST の worked examples

追補は source-order CST tree を示すが byte-range 付き tree はない。ここでは range を作らない。

```text
a[i; j].(x, y).{left: value, ..rest}
```

設計文書 10396–10430 行は distinct IndexTail、ProjectionTupleTail、ProjectionRecordTail sibling が delimiter、general-expression item、punctuation、close を直接所有する complete tree を与える。

```text
a[0]
```

設計文書 10216 行は tail grammar が維持する historical single-index fixture を記録する。

```text
a.(x)
```

設計文書 10284–10285 行は adjacent dot/opener を FieldTail でなく projection として固定する。

```text
a.{..left, middle, ..right}
```

設計文書 10496–10499 行は parser-valid な first/middle/last multiple spread item を固定する。各 item は field syntax でなく `ProjectionRecordSpreadItem` である。

## 6. Parser 側 AST shape

`FixedPostfixTail` は `Index(IndexTail)` と `Projection(ProjectionTail)` を追加する。`IndexTail` は正確に `open`、ordered `items`、recovered `close`、`range` を持つ。

`ProjectionTail` は正確に `Tuple(ProjectionTupleTail)` または `Record(ProjectionRecordTail)`。`ProjectionTupleTail` は正確に `dot`、`open`、ordered `items`、recovered `close`、`range` を持つ。`ProjectionRecordTail` も正確に `dot`、`open`、ordered `items`、recovered `close`、`range` を持つ。

`ProjectionRecordItem` は正確に `Expression(OperatorChain)` または `Spread(ProjectionRecordSpreadItem)`。`ProjectionRecordSpreadItem` は正確に `marker`、recovered boxed `rhs`、`range` を持つ。AST は separator punctuation/trivia を duplicate せず、generic Projection CST wrapper はない。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| `a[]`、`a.()`、`a.{}` | valid empty tail。Missing なし |
| leading/repeated comma または semicolon | punctuation 前に zero-width missing item 一件。punctuation を保持して retry |
| separator なし same-line next NUD | zero-width missing separator 一件後 same-position retry。valid ML は one item のまま |
| ordinary NUD/spread 前の malformed item | maximal non-empty item Error 一件後 same-slot retry |
| EOF/caller boundary の missing matching close | zero-width close Missing 一件。boundary は非消費 |
| stray mismatched close | caller-owned close を保持。そうでなければ closing Error 一件を consume して close slot 継続 |
| `a.{..}` / `a.{.., next}` | marker を保持し spread-RHS Missing 一件。separator/close は非消費 |
| `a.{..@rest}` | non-empty spread-RHS Error 一件後 `rest` を same RHS slot で retry |
| `a.{...rest}` / `a.{..+rest}` | longer spelling を DotDot へ split せず ordinary malformed/dynamic authority へ残す |
| item 内 malformed colon tail | nested ColonApplicationTail が一度 recover。projection は duplicate record を出さない |

Missing は全て zero-width、Error は maximal non-empty range、committed recovery node 一つは diagnostic identity 一つである。

## 8. Boundary と state-restoration contract

accepted opener ごとに matching delimiter、item stop、indentation baseline、typed expression-delimited owner を push し、normal/recovery/rollback exit で全 frame を exact に pop する。owner frame は ParenthesizedExpression と tuple projection、BracedStatementBlock と record projection のような same delimiter construct を区別する。nested punctuation/lexical region、ambient boundary、outer close、equal-or-shallower newline は item recovery scanner が consume しない。

## 9. Yulang2 divergences

Yulang3 は Yulang2 `Index > Bracket`、`ProjectionTuple > Paren`、`ProjectionRecord > BraceGroup` wrapper layer を削り、typed tail node が delimiter/item/close を直接所有する。separator wrapper でなく raw byte、typed Missing/Error recovery、longer spelling を split しない exact maximal DotDot、chain role による tail name を使う。adjacency、general expression content、semicolon、record-only spread の source acceptance は一致する。

## 10. Known residual / deferred surface

documented `ASOB-G` caller-boundary residual は hidden にせず characterize する。semantic index/projection meaning、record shape/type validation、spread position/multiplicity validation、target association、HIR lowering、inference、diagnostics、formatting は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `recognize_fixed_postfix`、`parse_fixed_postfix_tail`、`parse_index_tail`、`parse_projection_tuple_tail`、`parse_projection_record_tail`、`parse_projection_items_ast`、`commit_fixed_postfix_tail`、`commit_index_tail`、`commit_projection_tuple_tail`、`commit_projection_record_tail`、`commit_projection_items`、`index_item_error_retry`、`projection_item_error_retry`、`emit_index_missing`、`emit_projection_missing`、`emit_projection_close_missing` を参照する。

fixture は `index_tails_are_flat_layout_delimited_and_bp_neutral`、`index_tail_requires_adjacency_and_recovers_locally`、`index_tail_restores_owner_frames_and_precedes_terminal_colon`、`projection_tails_precede_field_dispatch_and_keep_general_expression_items`、`projection_tail_recovery_keeps_typed_slots_local`、`projection_tail_close_recovery_is_owner_safe_on_both_paths`、`record_projection_rejects_non_exact_spread_spellings`。
