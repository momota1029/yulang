# 現在のタスク: yu-syntax parser構築の継続とgrammar/CST正規化サイトの起票

更新: 2026-08-24

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

## 既知の未修正バグ(2026-08-24発見、今回のpositional fence作業とは無関係)

`crates/yu-syntax/src/grammar/type_expr/polymorphic_variant.rs`の`classify_tag_boundary`が、
壊れたバイトが一切ない正当な複数tag多相variant型本体(例: `:{\n  A Pair(Int);\n  B\n}`)を、
active `StopKind::Newline`下でparseすると、1つ目のtagで止まってしまう
(`active_stop_set(i).contains(StopKind::Newline)`を無条件にownerへのyield理由として扱ってる)。

positional fence機構のGate 10 false-positive fixture作成中に発覚。commit `a0365f98`
(fence作業着手前)の時点で同一コードが既に存在してたと確認済みで、fenceとは無関係な既存バグ。
未着手、優先順位未確定。

## 次の候補(優先順位未確定、着手時に選ぶ)

1. **standalone `TypeExpression`の各use-site配線(残り)**: struct field・cast宣言・role
   signature・where節・act signature等。pattern型注釈は完了、残りが本体作業。
2. **canonical Statement / root Declarationの残りvariant**: `type`/`struct`/`enum`/
   `error`/`role`/`impl`/`cast`/`act`/`for`文/演算子定義/`where`/doc-comment宣言。
   `mod`宣言完了時点の調査で、`mod`と`for`以外は全部standalone TypeExpression待ちで
   blockedと判明済み——1が先に進めば大半が着手可能になる。
3. **grammar/CST/エラー回復の正規化サイト**(下記TODO参照)。
4. **polymorphic variant複数tag+active newline境界バグ**(上記参照)。

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
