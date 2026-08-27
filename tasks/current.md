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
3. **grammar/CST/エラー回復の正規化サイト**(下記TODO参照)。
4. **defer済み4 familyの優先順位決定**: derives ownerの拡張(Enum/Error/Act)・
   Type-attached `impl`(`type Name impl ...`)・shared declaration companion `with:`・
   Type colon/brace role-like body。正本はどれも「別addendumへ」としか書いておらず、
   相対的な実装順序は未決定。
5. **Cast known-residualの一般化解消**: 追補が明示的に別addendum送りにした、caller
   boundary hidden behind a missing nested delimiterというcondition-based residual
   family(ASOB追補由来、Castで再確認)。nested Pattern/TypeExpressionへのcaller
   boundary伝播・missing delimiter・local candidate/same-spelling separator priorityを
   一般化する新しいsigned addendumが必要。

## TODO: 文法・CSTをエラー含めて完全に規格化するサイトを作る

ユーザ指示(2026-08-23): 「これまでの文書は非常に貴重な資料です。文法・CSTをエラー含めて
完全に規格化してウェブサイトを作るTODOが欲しい」

### 背景

`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`は現時点で16,000行超。個々の
grammar要素ごとに、次を単一の正本箇所として持つ設計になっている(多相variant型・bracket
row型の設計サーガで確立した「single canonical statement」規律):

- 文法(BNF相当の構文規則)
- CST shape(worked exampleでtrivia byteまで明示)
- AST shape(Rust struct定義)
- typed recovery contract(Missing/Errorの発火条件・range・retry位置を網羅する表)
- yulang2からの意図的divergence一覧

これは「実装のための設計文書」であって、「読者(言語ユーザ・ツール開発者)向けの参照資料」
ではない。後者を作るには、この一次資料から要約・整形・横断索引化する変換作業が要る。

### スコープ(仮、着手時に確定)

- 各grammar要素(tuple・operator chain・if/elsif/else・pattern各種・TypeExpression
  各primaryなど)について、次を1ページで示す:
  - 構文規則(BNF or railroad diagram相当)
  - 正常系のCST例(trivia込み)
  - 各recovery行(どんな壊れたsourceがどんなMissing/Errorになるか、before/after)
- yulang2との既知のdivergence一覧(意図的なものだけ・理由付き)
- 実装ファイルへのクロスリファレンス(`crates/yu-syntax/src/grammar/*.rs`のどの関数が
  どのgrammar要素を担当するか)

### 未確定事項(着手時にユーザと相談)

- サイトの技術基盤: 既存の`web/`(yulang2時代のplayground/docsサイト)を拡張するか、
  別立てにするか。yulang3ではdocs/playground自体まだ存在しない
  (`docs/yulang3-architecture.md`の§15参照——実装が進んでからサルベージする方針)。
- 生成方式: 設計doc(Markdown)から自動抽出するか、手動でページを書き起こすか。
  現在の設計docはprose(自然言語)中心でmachine-readableな構造化データではないため、
  完全自動化は難しく、半自動(正本docを参照しながら人力で整形)が現実的と見られる。
- 対象読者: 実装者向け(このセッションの開発者)か、将来の言語ユーザ向けか——後者なら
  文体・省略レベルが大きく変わる(`notes/style/writing-rhythm-guide.md`のpage-layer
  assignmentが関係する)。
- 着手タイミング: grammar自体がまだ全部確定していない(use-site配線・残りdeclaration
  文が未着手)。全部確定してから一括で作る方が手戻りが少ないか、要素ごとに確定次第
  ページ化していくか。

### 次にやること

着手する時は、まずこのTODOをEnterPlanModeまたはAskUserQuestionでスコープ確定してから
着手する。現時点では起票のみ。
