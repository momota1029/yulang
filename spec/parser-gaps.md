# パーサの未実装・仕様との差

仕様（`spec/`）が約束している形のうち、現在の構文解析器（`crates/yu-syntax`）がまだ読めない・扱えない形の台帳。
パーサを触るときの TODO で、仕様の状態とは別に管理する。確かめ方: `parse_file` に演算子の宣言を前置きしたソースを渡し、CST に `Error` / `Missing` / `Invalid` が出ないかを見た。

## 読めない形

**なし**（2026-11-04）。`spec/` の章 1〜9 に載せた構文例 80 個は、すべて `Error` / `Missing` / `Invalid` なしで読める。
経緯と設計判断は `notes/design/2026-11-04-parser-gap-closure-addendum.md`（Authoritative）に残してある。

## 意図的に残している未完了

- `yulang` として選ばれた Yumark のコード fence の**本文**: 開き・info・境界だけを出し、本文のイベントは convergence gate まで延期（設計メモ §6）。
- Yumark の埋め込み Yulang について、AST と direct CST の等価性の証明と gate 3・4 の完了認定は O6 まで延期（`2026-09-07-successor-t2a-yumark-evidence-timing-correction.md`）。
- 出力先を trait object（`SyntaxOutput`）にした影響の速度測定（gate 7）。

## 読めると確かめた形

コメント `//` と `/* */` と doc コメント（`--`、`---`）、`if` / `elsif` / `else`、字下げによる式の継続、`f(x)` / `f (x)` / `f: x`、演算子の宣言、
`my` / `our` / `pub` の binding、`mod`（ファイル形式を含む）、`use`、`x.foo::bar`、`xs[0]`、`(1, 2).0`、`f()`、`with:`、
literal（整数、小数、文字列、list、record、tuple）、`$x` / `&x`、label、`case` / `catch`（guard、or・as、裸の名前の適用、`~"..."`、型注釈つき）、
lambda（複数引数、pattern 引数）、`sub:`、`for`、`do`、`type`（alias と `with:`）、`struct`（型引数、tuple struct）、`enum`、`act`、`act copy`、`error`、`role`、`impl`、`where`、`cast`、型注釈、範囲、パイプ、`rule { }`、`~"..."`。
