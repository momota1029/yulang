# パーサの未実装・仕様との差

仕様（`spec/`）が約束している形のうち、現在の構文解析器（`crates/yu-syntax`、2026-11-04 時点）がまだ読めない・扱えない形の台帳。
パーサを触るときの TODO で、仕様の状態とは別に管理する。確かめ方: `parse_file` に演算子の宣言を前置きしたソースを渡し、CST に `Error` / `Missing` / `Invalid` が出ないかを見た。

## 読めない形（実装の穴と見ているもの）

| 項目 | 仕様の根拠 | 現在のパーサ |
| --- | --- | --- |
| 式の中の label（`'done.return 42`、`last 'outer`、`sub 'done:`） | [章3c.3](03c-control.md) | `for 'x`、`case 'c 3:` の見出しは読める。`sub 'done:`、`last 'outer` は Error |
| list literal（`[]`、`[1, 2]`、`[1, ..xs]`） | [章3.1](03-expressions.md) | `[` が Error（pattern の list は読める） |
| 小数 literal（`1.5`、`1e3`） | [章3.1](03-expressions.md) | `1` の後ろの `.5` / `e3` が Error |
| 位置 field（`(1, 2).0`、`id.0`） | [章4.4](04-types.md) | `.` の後ろの `0` が Error |
| 参照の読み出しと更新（`$count`、`&count = v`） | [章3c.6](03c-control.md) | 式の中の `$x`・`&x` は Error。`my $count = 0` の束縛は読める |
| `struct` の型引数（`struct pair 'a { ... }`） | [章4.4](04-types.md) | `'a` が Error（型引数のない `struct` は読める） |
| `case` の arm の parser pattern（`~"GET :x" -> ...`） | [章9.1](09-parser-dsl.md) | `~` が Error（式としての `~"a"` と `rule { }` は読める） |
| 複数引数の lambda（`\x y -> x`） | [章3.4](03-expressions.md) | 文頭で Error（単項 `\x -> x` は読める。素材では「unary lambda の admission」まで） |
| 裸の名前を頭にした pattern の適用（`just x -> ...`、`op x, k -> ...`） | [章3b.1](03b-patterns.md)、[章5.2](05-effects.md) | `Missing`。`opt::just x`、`just(x)`、`op(x), k` は読める |
| arm の pattern の型注釈（`x: int -> ...`） | [章3b.7](03b-patterns.md) | `->` が型の矢印と衝突して `Missing`。`(x: int) -> ...` なら読める可能性（未確認） |
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
