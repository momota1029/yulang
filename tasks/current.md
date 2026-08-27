# 現在のタスク: yu-syntax parser構築の継続とgrammar/CST正規化サイトの起票

更新: 2026-08-27（cast宣言13 gate完走）

このファイルは、着手中または直ちに着手できる作業だけを置く。完了履歴はGit、設計判断は
`notes/design/`が正本。yulang3branchでは`tasks/`・`notes/progress/`を一旦削除してまっさらに
したため、このファイルが最初の再作成。

## 現在地

`crates/yu-syntax`はchasaベースのrecursive-descent parserとして、2026-08-20の
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`を正本に構築中。

- tuple・演算子CST・colon application・if/elsif/else・brace statement block・pattern文法・
  case/catch・list/record pattern・call/field/path/ML-application・generic-expression
  WithBodyTail・canonical Statementのbinding/use拡張・`mod`宣言、が実装・push済み。
- standalone `TypeExpression`文法(pattern.rsと同じ立ち位置の独立grammar、`OperatorTable`
  非依存)が着地し、core grammarに加えて5つのexotic primary形式
  ——named record型・forall型・effect row型・多相variant型・bracket row grammar——
  全部Authoritative(ユーザ承認済み)。
- `Pattern : TypeExpression`型注釈wiring(最初のuse-site)がAuthoritative設計どおり実装・
  push済み。実装レビュー中に発覚したTypeExpression共有malformed recovery scannerの
  newline境界バグを発端に、`TMN-B/P/C/S`(newline owner policy)追補と、その実装の
  owner-boundary-safety配線漏れ(3巡連続で発見)を根本解決する`positional fence`追補
  (`ParseLocal`-scoped ambient state、bool手渡し方式を完全に置換)を設計・実装・多重レビュー
  済み。全12 implementation gate完走、390 tests green。
- 多相variant型は設計10巡・実装7巡を要した。教訓は
  `/home/momota1029/.claude/projects/-home-momota1029-rust-yulang/memory/feedback-two-level-judge-needs-shared-driver.md`
  に記録済み(二層judgeはAST/direct-CST両pathを別々に手書きせず、最初から共有driver+薄い
  adapterで書く)。
- `StructDeclaration`/`TypeDeclaration`共有の`derives`clause attachment文法(DRV-G/J/T/R、
  9 gate)がAuthoritative設計どおり実装・push済み。Gate 1a(neutral TypeExpression episode
  infrastructure)は後続addendumからも再利用可能な形で切り出した。Gate 8(実dispatch
  promotion)でCatch-inline文脈のambient newline所有権バグを発見・修正。
- standalone `impl`宣言shell文法(IMD-G/J/T/R、9 gate)がAuthoritative設計どおり実装・
  push済み。derivesのGate 1aに依存。Gate 6(recovery matrix)で4件、Gate 7
  (state-restoration matrix)で2件、実バグを発見・修正(いずれもisolated adapter局所、
  共有TypeExpression episode機構自体は無傷)。Type-attached `impl`・`with:` companion・
  Type colon/brace role-like body・Impl-specific `via`は別addendumへ明示的にdefer。
- standalone `cast`宣言文法(CAST-G/J/T/R、13 gate計画)がAuthoritative化済み(2026-08-27)、
  同日中に全13 gate(1・2・3a-i/ii/iii・3b・4a/4b・5・6・7・8・9)を実装・push完了、511
  tests green。yulang2の`cast(x: from_ty): to_ty = body`構文を土台に設計。設計レビューは
  11巡を要した(derives 5巡・impl-shell 3巡より大幅に多い)——CastのPattern-slot recovery
  がPattern annotation・nested delimiter・arm-sequence newline authorityと絡む部分が
  難所で、round 4〜7は既知residualの正確な境界線を閉じた表からcondition-based記述へ
  転換する過程、round 8〜10はGate 3の実装契約(shared driver・outer_stops伝播範囲)の
  精密化だった。実装でもGate 3bが7回の委譲(Terra 5回連続非収束→Sol xhighへエスカレーション)
  を要した最難関gateで、`cast((x @): B;`のようなnested Parenthesized回復後にCast自身の
  target colonがPattern本体の型注釈へ誤飲込まれる本質的な合成バグを発見・解決
  (`PatternMandatorySlotPolicy`に`recovered_primary_tail_stops`フィールドを追加)。
  副産物でPattern本体の既存バグ(`ParenthesizedPattern`のAST/direct不一致、`c852d878`
  まで遡る既存gap)も発見し、Gate 3a-iiで修正。Gate 4aでBinding-style body layout
  decisionを`classify_binding_style_body_layout`/`parse_binding_style_body`/
  `commit_binding_style_body`として中立化、derives/implに続く3例目の共有infra切り出し。
  Gate 8(atomic dispatch promotion)は`recognize_statement_intro`のImpl後/Binding前へ
  挿入、既存non-Cast優先順位・fixtureは無傷。Cast-specific `via`・rule登録・暗黙変換適用・
  expected-type境界処理・coherence・HIR/resolver/inference/formatterは明示的にscope外
  (Gate 9でworkspace全体grepにより未実装を確認済み)。既知residual(caller boundary hidden
  behind a missing Cast-contained Pattern/TypeExpression delimiter、four-condition
  predicate)はGate 8/9で6件のrepresentative fixtureとしてcharacterize済み・未解決のまま
  残す方針(closed tableではなくcondition-based)。

## 既知の未修正バグ

なし。旧「多相variant複数tag+active newline境界バグ」(`classify_tag_boundary`が
`active_stop_set(i).contains(StopKind::Newline)`を無条件にownerへのyield理由として
扱ってた件)は、commit `f4332308`(2026-08-26)で修正・回帰test
(`qualifying_tag_newline_remains_local_under_an_active_newline_stop`)化済み。

## 次の候補(優先順位未確定、着手時に選ぶ)

1. **standalone `TypeExpression`の各use-site配線(残り)**: role signature・where節・
   act signature。pattern型注釈・struct field・cast(実装完了)は完了、残り3件が本体作業。
2. **canonical Statement / root Declarationの残りvariant**: `enum`/`error`/`role`/
   `act`/`for`文/declaration-level `where`/doc-comment宣言。`type`/`struct`/`mod`/
   `impl`(shellのみ)/`cast`/演算子定義は完了。
   derives・impl・castが着地した今、role/impl/enum系のownerがそれらの共有driverを
   どこまで再利用できるか、着手前に要調査。
3. **grammar/CST/エラー回復の正規化サイト**: pilot稼働中(下記参照)。次はexpressions/
   patterns/typesの各elementページを1つずつ追加していく。
4. **defer済み4 familyの優先順位決定**: derives ownerの拡張(Enum/Error/Act)・
   Type-attached `impl`(`type Name impl ...`)・shared declaration companion `with:`・
   Type colon/brace role-like body。正本はどれも「別addendumへ」としか書いておらず、
   相対的な実装順序は未決定。
5. **Cast known-residualの一般化解消**: 追補が明示的に別addendum送りにした、caller
   boundary hidden behind a missing nested delimiterというcondition-based residual
   family(ASOB追補由来、Castで再確認)。nested Pattern/TypeExpressionへのcaller
   boundary伝播・missing delimiter・local candidate/same-spelling separator priorityを
   一般化する新しいsigned addendumが必要。

## 文法・CSTをエラー含めて完全に規格化するサイト(`syntax-reference/`、pilot稼働中)

ユーザ指示(2026-08-23)で起票、2026-08-27にスコープ確定・pilot実装・push完了
(commit `cc25bc2e`)。

### 決定事項(2026-08-27、AskUserQuestionで確定)

- 技術基盤: **mdBook**。`web/`(yulang2時代のplayground/docsサイト、yulang3では
  一括削除済み)は再利用しない。`cargo install mdbook`でこの環境に導入済み。
- 設置場所: 新規`syntax-reference/`(`docs/`のarchitecture文書とは責務分離)。
- 対象読者: **実装者向け**(このセッションの開発者・将来のClaude/Codexセッション)。
  文体は簡潔・省略多め、実装ファイルへのクロスリファレンス重視。
- 着手タイミング: **grammar確定を待たず、要素ごとに確定次第ページ化**。TypeExpression
  残りuse-site・declaration残りvariantが未着手でも並行して進める。
- 生成方式: 正本(`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`)からの
  半自動抽出。Codex(Terra、要素ごとの内容は正本から機械的に転記する作業のため)が
  1ページずつ執筆し、Claudeが実装ファイル・commit履歴と照合してfaithfulness検証する
  運用。

### サイト構成

```text
syntax-reference/
  book.toml
  README.md
  src/
    SUMMARY.md
    index.md
    conventions/   # Parser共通規約(trivia/range/AST-direct parity等、stub)
    expressions/
    patterns/
    types/
    statements/     # pilot: bare-nominal-type.md 完成
    cross-cutting/
    indexes/
```

各elementページの11節template: Status/正本/last-verified commit → Scope →
BNF grammar → judge/priority/owner boundary → byte-exact CST worked example →
AST shape → typed recovery table → boundary/state-restoration contract →
yulang2 divergence → known residual/deferred surface → 実装関数・fixture
cross-reference。

### pilotページの検証結果

`statements/bare-nominal-type.md`(bare nominal `type`宣言、9 gate完了済み)を
pilotとして選定・作成。Claudeが独立に照合し、引用した実装関数8件・回帰test 7件が
全部実在、AST struct shapeが実装と完全一致、引用commit hash 10件が全部正しい
gate commitを指す、正本の行範囲引用(19677–20277)がbyte-precise、worked
example 2件が正本から実際に転記されたものであることを確認済み。

### 次にやること

expressions/patterns/typesの各elementから1つずつページを追加していく。優先順位は
未確定——着手時に選ぶ。tuple/operator chainのように複数の正本節を合成する要素は、
1ページに統合せずcross-cuttingページ参照にする方針(Sol提案どおり)。
