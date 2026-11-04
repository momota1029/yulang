# パーサの未実装・仕様との差

仕様（`spec/`）が約束している形のうち、現在の構文解析器（`crates/yu-syntax`、2026-11-04 時点）がまだ読めない・扱えない形の台帳。
パーサを触るときの TODO で、仕様の状態とは別に管理する。確かめ方: `parse_file` に演算子の宣言を前置きしたソースを渡し、CST に `Error` / `Missing` / `Invalid` が出ないかを見た。

## 読めない形（実装の穴と見ているもの）

| 項目 | 仕様の根拠 | 現在のパーサ |
| --- | --- | --- |
| `--` / `---`（doc コメント） | [章1.2](01-lexical.md) | `-` が Error。`//` は読める |

## 仕様の側を見直す候補（パーサの実装が意図的かもしれないもの）

- 複数引数の lambda、裸の名前を頭にした pattern の適用、`--` の doc コメントは、パーサの設計判断で今の形になっている可能性がある。
  仕様の側を変える必要があるかは、ユーザーの判断を待つ（章3.4、章3b.1、章1.2）。

## 読めると確かめた形

コメント `//` と `/* */`、`if` / `elsif` / `else`（インデントと波括弧）、字下げによる式の継続、`f(x)` / `f (x)` / `f: x`、演算子の宣言（`prefix` / `infix` / `lazy infix` / `suffix`）、
`my` / `our` / `pub` の binding、引数付き binding、`our p.m = ...`、`mod name:`、`mod test:`、`use`（group、glob、`without`、`as`、`(+)`）、
`x.foo::bar`、`xs[0]`、`f()`、`with:`、`case`（guard の `if` / `where`、label の `case 'c 3:`、or・as pattern、tuple・record・list・symbol・polyvariant pattern）、
`catch`、`sub:`、`for`（label つき）、`do`、tuple・record literal、record spread、`type`（alias と `with:`）、tuple struct、brace の `struct`、`enum`（`=` 形と字下げ形）、
`act`、`act copy`、`error`、`role`（associated type を含む）、`impl`、`where`、`cast`、型注釈（binding、引数、返り値、`as`）、範囲 `0..10` / `0..<10`、パイプ `|`、文字列の補間、`rule { }`、`~"..."` の式。
