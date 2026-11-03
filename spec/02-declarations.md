# 章2 binding・可視性・module

状態の凡例は [README](README.md)。この章は binding、可視性（`my` / `our` / `pub`）、`mod`、`use` を扱う。
データ型（`struct` / `enum` / `type`）は章4、`act` は章5、`role` / `impl` / `cast` は章6 で書く。
`realm` / `band` と `test` module は、範囲を決めてから書く（確認 C7, C8）。

## 2.1 binding　〔要確認〕

```yulang
my x = 1
our answer = 42
pub exported = answer
```

関数の引数は binding の頭部に直接書ける。これは**カリー化された lambda の糖衣**である。

```yulang
my add x y = x + y
// 同じ意味:
my add = \x -> \y -> x + y
```

- block は文を順に評価し、最後の式を値として返す（式指向）。
- 宣言だけで本体のない `pub declared` の形がある。意味は未確認（確認 C5）。
- `our p.norm2 = ...` のように名前に dot を含む binding は **method の定義**になる。意味は章4・章6 で書く。

出典: `main:docs/language/overview.ja.md` §block と binding、`main:notes/design/yulang-language-report.md` §5.1

## 2.2 可視性: `my` / `our` / `pub`　〔要確認・最重要〕

| 語 | 見える範囲（素材から起こした仮説） |
| --- | --- |
| `my` | その module の中だけ（private）。local binding は字句的な local |
| `our` | 囲んでいる companion module へ出る。`with:` の method や `act` の operation に使う |
| `pub` | module の外へ出る。加えて、その値を module 自身の「型 pane」にも公開する |

```yulang
struct point:
    x: int
    y: int
with:
    our p.norm2 = p.x * p.x + p.y * p.y    // companion へ出る
```

- `with:` の中では `our` も `pub` も、companion 経由で他の module から見える。違いは `pub` が型 pane にも出ることだけ。
- module の外へ出す top-level の helper は `pub` を使う。
- 現状の実装は、`our` と `pub` の差を**アクセス判定だけ**ではほとんど区別していない。意図の明文化が要る。

出典: `main:web/docs/ja/guide/pitfalls.md`「`our` と `pub` の違い」、`main:notes/design/yulang-language-report.md` §5.2
注意: 「型 pane」が何を指すか（hover の表示か、型の公開面か）は、素材だけでは判断できなかった（確認 C5）。

## 2.3 `mod`　〔要確認〕

```yulang
mod geometry:
    pub origin = (0, 0)

geometry::origin
```

```yulang
mod helper;        // 同階層の helper.yu（または helper/mod.yu）を子 module として読む
pub mod helper;    // どちらの形にも可視性を付けられる
```

- inline の `mod` は nested module を作る。ファイル形式の `mod name;` は `name.yu` を子 module として読み込む。
- module 内の path は `::` で辿る。

出典: `main:web/docs/ja/reference/modules.md`

## 2.4 `use`　〔要確認〕

```yulang
use std::data::list::map
use std::core::ops::{(+), (-)}
use my_module::old_name as new_name
use noisy::* without debug
```

| 形 | 意味 |
| --- | --- |
| `use path::name` | 名前を scope に入れる |
| `use path::name as alias` | 別名で入れる |
| `use path::*` | 見えているものを全部入れる |
| `use path::{a, b as c, (+)}` | group。演算子は `(+)` と括弧で書く |
| `use path::* without a, (+)` | glob から除く |

- 演算子の宣言は、`use` で import したファイルだけでその演算子が読める（章1.5）。
- 通常の entry file には `use std::prelude::*` が暗黙に付く。

出典: `main:web/docs/ja/reference/modules.md` §use、`main:notes/design/yulang-language-report.md` §3.1, §3.3

## 2.5 companion module　〔要確認〕

`struct`、`type ... with:`、`enum`、`act`、`error`、`role` は、**同名の companion module** を作る。
body の中の `our` / `pub` はそこへ入る。`enum` / `error` の variant と `act` の operation も companion の member になる。

```yulang
opt::just 1
out::write "hi"
```

prelude が `just` / `nil` / `ok` / `err` のような標準 variant を re-export するので、通常は修飾なしで書ける。

出典: `main:web/docs/ja/reference/modules.md` §Companion module

## 確認してほしい点

- **C5** `my` / `our` / `pub` の意味を、あなたの言葉で確定してほしい。特に次の 2 つ。
  - `our` と `pub` の違い。素材では「`pub` は module 自身の型 pane にも公開する」とあるが、「型 pane」とは何か。
  - 本体のない `pub declared` の意味。
- **C6** カリー化 lambda への糖衣（`my add x y = ...` ≡ `\x -> \y -> ...`）は仕様として約束してよいか。
  多引数の関数が内部で本当にカリー化されるのか、それとも引数リストを持つのか。
- **C7** `realm` / `band`（version 付きの解決空間と import の島）を仕様に入れるか。素材では「実験中」とされている。
  入れないなら、この章では「module path は current band の中」とだけ書いて詳細は後回しにする。
- **C8** `mod test:` / `mod test name:`（`yulang test` が実行する test module）は言語仕様か、処理系（ツール）の機能か。
