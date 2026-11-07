# パーサの未実装・仕様との差

仕様（`spec/`）が約束している形のうち、現在の構文解析器（`crates/yu-syntax`）がまだ読めない・扱えない形の台帳。
パーサを触るときの TODO で、仕様の状態とは別に管理する。確かめ方: `parse_file` に演算子の宣言を前置きしたソースを渡し、CST に `Error` / `Missing` / `Invalid` が出ないかを見た。

## 読めない形

**なし**（2026-11-04）。`spec/` の章 1〜9 に載せた構文例 80 個は、すべて `Error` / `Missing` / `Invalid` なしで読める。

**2026-11-07 に見つかった 5 件は閉じた**: lambda の record 引数（`\{x, y} -> x`）、式としての record の spread（`{x: 1, ..rest}`）、対象なしの `case:`、`case` と `catch` の 2 番目以降の arm が隣接した `-` と整数で始まる形（`-1 -> 2`）、`act` の operation の署名の下の `where`。
構文ガイドの例の検査で見つかり、`notes/design/2026-11-07-parser-gap-closure-addendum-2.md`（Authoritative）の WP-12〜15 と WP-17 で直した。
同日確定した対象なしの`catch:`も、同じ追補のWP-16で対応した。
経緯と設計判断は `notes/design/2026-11-04-parser-gap-closure-addendum.md`（Authoritative）に残してある。

## 回復の弱点（2026-11-07 に観測、未対応）

閉じていない括弧が、後ろの文を全部その中の項目として吸う。列 0 の宣言のキーワード（`my`）は、開いている括弧を閉じる合図になっていない。
再現と影響、直す案は `notes/ideas/2026-11-07-error-tolerance-status.md`。文法と回復の設計判断なので、ユーザーの承認と追補が要る。

## 意図的に残している未完了

- `yulang` として選ばれた Yumark のコード fence の**本文**: 開き・info・境界だけを出し、本文のイベントは convergence gate まで延期（設計メモ §6）。
- Yumark の埋め込み Yulang について、AST と direct CST の等価性の証明と gate 3・4 の完了認定は O6 まで延期（`2026-09-07-successor-t2a-yumark-evidence-timing-correction.md`）。
- 出力先を trait object（`SyntaxOutput`）にした影響の速度測定（gate 7）。

## 読めると確かめた形

コメント `//` と `/* */` と doc コメント（`--`、`---`）、`if` / `elsif` / `else`、字下げによる式の継続、`f(x)` / `f (x)` / `f: x`、演算子の宣言、
`my` / `our` / `pub` の binding、`mod`（ファイル形式を含む）、`use`、`x.foo::bar`、`xs[0]`、`(1, 2).0`、`f()`、`with:`、
literal（整数、小数、文字列、list、record、tuple）、`$x` / `&x`、label、`case` / `catch`（guard、or・as、裸の名前の適用、`~"..."`、型注釈つき）、
lambda（複数引数、pattern 引数）、`sub:`、`for`、`do`、`type`（alias と `with:`）、`struct`（型引数、tuple struct）、`enum`、`act`、`act copy`、`error`、`role`、`impl`、`where`、`cast`、型注釈、範囲、パイプ、`rule { }`、`~"..."`。

## G12 doc コメントの後ろ向き付与とメンバーへの付与（2026-11-04 起票）

- 仕様: `spec/01-lexical.md` §1.2。同じ行の末尾 `-- ...` と `=` 直後の `-- ...` が、その行で始まった宣言の doc になる。
- struct の field / enum の variant / role の method / act の operation にも、直前行・行末・`=` 直後の doc が付く。
- 現状: 直前行の doc だけ（WP-11 gate 6）。行末・`=` 直後・メンバーは未対応。

## G13 数値 literal の形（2026-11-04 起票、未確認）

- 仕様: `spec/03-expressions.md` §3.1。`_` 区切り、`0x`/`0b`/`0o`、指数（`1e3`、`1.5e-2`）。`1.` と `.5` は書けない。
- 現状: 字句解析器に該当処理が見つからない。実 parser で例を通して確かめてから着手する。


## 実 parser での仕分け結果（2026-11-04、`spec/parser-gap-cases.txt` の 38 例）

実 parser（`parse_file`、演算子は `+ - * < |` だけ宣言）で、`structural_recoveries()` が空かどうかを見た。
例の入力は `spec/parser-gap-cases.txt`（`=====` 区切り、1 行目が名前）。

### 読めない（実装する）

| 番号 | 内容 | 例の名前 |
| --- | --- | --- |
| G12 | doc コメントの行末・`=` 直後・メンバー（field）への付与 **（完了 2026-11-04。gpt-6.1-terra で 2 回止まり、gpt-6.1-sol/xhigh で完了。yu-syntax 1587 + 統合11 緑。付与された doc は `BindingStatement` / `StructField` / `EnumVariant` の直接の子 `DocCommentDeclaration`）** | doc-trailing, doc-after-eq, doc-member-field |
| G13 | 数値 literal の `_` 区切り・`0x`・`0b`・`0o` **（完了 2026-11-04、gpt-6-luna、yu-syntax 1567 + 統合11 緑）** | num-underscore, num-hex, num-bin |
| G14 | 空の block `{;}` **（完了 2026-11-04、gpt-6-luna、yu-syntax 1561 + 統合11 緑）** | empty-block |
| G15 | range pattern `0..10`、`1..`、`..0` **（完了 2026-11-04。Luna は途中で降りたので gpt-6.1-terra/high で完了。yu-syntax 1578 + 統合11 緑。新 SyntaxKind `RangePattern`）** | range-pat, range-pat-lower, range-pat-upper |
| G16 | lambda の `&` 引数 `\&a -> ...`（`&a::run` を手で呼ぶ形）**（完了 2026-11-04、gpt-6-luna、yu-syntax 1579 + 統合11 緑。実際に読めなかったのは lambda の括弧なし引数だけ）** | ref-run |
| G17 | struct の field default `y: int = 4` **（完了 2026-11-04。Luna は途中で降りたので gpt-6.1-terra/high で完了。yu-syntax 1565 + 統合11 緑）** | struct-default |
| G18 | variant 型の `\|` 形 `:ready \| :some int` | variant-type-bar |

### 読める（parser は追加不要）

`1e3`、`1.5e-2`、`our use`、`pub use`、`{x: 1,}`、`{x, y}`、`{x,}`、`{}`、`(1,)`、複数行文字列 `"""`（構文のみ。字下げの意味は別）、
`%x{255}` `%8.3{t}`、guard の `if`、`'count.again`、`my $c = 0`、`my &c = &d`、`with:`、`|`、`xs[0]`、`v.(x, y(4))`、`v.{first: x}`、
`if` の else 無し、`mod helper;`、`:{ready, some int}`。

### 読めるが仕様が約束しない

- guard の `where`（`x where x < 0 -> ...`）も読める。仕様は `if` だけ（E19）。実装で拒否するかは後で決める。
- 複数行文字列の字下げの除去、`%{}` の書式の意味、`'count.again` の意味などは、構文が通るだけで意味は未実装。意味の実装は parser の外。

- G14 の補足: `{ ; 1 }`（先頭に `;` を置いて続きがある形）は今も読めない。仕様が約束していない形なので放置。

- G18 の補足（要フォロー）: 字句解析器の `scan_type_polymorphic_variant_colon` は、`:ident` の後に `| :tag` が来るかを `remainder.find('|')` で**ソースの残り全部**から探している。
  正しい入力には影響しないが（隣接 colon の束縛・返り値注釈は 5 例で確認済み）、不正な単独 `:tag` が多い入力では O(n²) になりうる。先読みを同じ型式の範囲に制限する小修正を後で入れる。
- G15 の補足: 負の bound（`-1..5`）は未検証。式の `..` / `..<` / `1..`、list/record の spread は 16 例で回帰なしを確認済み。

- G12 の補足:
  - 既存テストを 1 件だけ更新した（`doc_comment.rs` の role/act member の直前行 doc は、recovery なしで doc node を作る）。spec 1.2 規則 4 による。
  - `--` が演算子として宣言されているファイルでは、途中・行末の `--` は従来どおり演算子。
  - 式の途中や継続行の `--`（`my a = 1 + -- c`、`f x\n    y -- c`）は従来どおり recovery になる。**未決: これを無害なコメントとして読むか。**（spec 1.2 は「独立コメントのまま」と書いているが、実際は RawError。）
  - 直前行の doc は、struct の field では `StructDeclaration` の子（field の兄弟）として入る。
