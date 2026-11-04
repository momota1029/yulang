# 章2 binding・可視性・module

状態の凡例は [README](README.md)。この章は binding、可視性（`my` / `our` / `pub`）、`mod`、`use` を扱う。
データ型（`struct` / `enum` / `type`）は章4、`act` は章5、`role` / `impl` / `cast` は章6 で書く。
配布単位とコード塊の単位（`realm` / `band`）は 2.6 に最小限で書く。

## 2.1 binding　〔カリー化は確定、他は要確認〕

```yulang
my x = 1
our answer = 42
pub exported = answer
```

関数の引数は binding の頭部に直接書ける。これは**カリー化された lambda の糖衣**である（確定, 2026-11-04）。関数は実際にカリー化される。

```yulang
my add x y = x + y
// 同じ意味:
my add = \x -> \y -> x + y
```

- **再帰と再束縛**（確定, 2026-11-04）: 引数のある binding（関数）は自分自身を呼べる。引数のない値 binding は自分自身を指せず、右辺の同名は既存の束縛を指す。
  同じ scope で同名の `my` を再び書くのは許され、後のものが前のものを隠す。

```yulang
my fact n =
    if n == 0: 1
    else: n * fact (n - 1)     // 自己再帰

my a = 1
my a = a + 1                    // 右辺の a は 1 行目の a。結果は 2
```

- **参照の順序**（確定, 2026-11-04）: 関数 binding どうしは書く順番に関係なく互いを参照できる（相互再帰できる）。値 binding は上から順に評価され、下で定義されるものは参照できない。

```yulang
my even n = if n == 0: true else: odd (n - 1)     // odd は下にあるが参照できる
my odd n = if n == 0: false else: even (n - 1)

my a = b + 1     // エラー: b はまだ定義されていない
my b = 2
```

- 関数の本体でも、値 binding は上にあるものしか参照できない（確定, 2026-11-04）。

```yulang
my f x = x + base      // エラー: base は下で定義されている
my base = 10
```

- block は文を順に評価し、最後の式を値として返す（式指向）。
- 素材にあった本体のない `pub declared` の形は、デバッグ用の名残りらしいので**仕様に採らない**（確定, 2026-11-04）。
- `our p.norm2 = ...` のように名前に dot を含む binding は **method の定義**になる。意味は章4・章6 で書く。
  書ける場所は `with:` の中に限らない。module のトップレベル、`role` や `act` の中にも書ける（確定, 2026-11-04）。
  何も要求しない method（`.tap` のように、どの型にも付けられるもの）もこの形で書く。

```yulang
our x.tap f = f x; x            // どの型にも付く method
our p.norm2 = p.x * p.x + p.y * p.y    // トップレベルに書いても method になる
```

  他の module の型にも method を足せる（確定, 2026-11-04）。method は定義した module の名前空間に入り、
  `use` で見えるようにしたものだけが `p.norm2` で選ばれる。同名の method を 2 つ `use` したら曖昧エラー（impl が複数候補のときと同じ）。

出典: `main:docs/language/overview.ja.md` §block と binding、`main:notes/design/yulang-language-report.md` §5.1

## 2.2 可視性: `my` / `our` / `pub`　〔確定〕

Rust の `let` に対応づけると次のとおり（確定, 2026-11-04）。

| 語 | Rust での対応 | 見える範囲 |
| --- | --- | --- |
| `my` | `let` | その module の中だけ（private）。local binding は字句的な local |
| `our` | `pub(crate) let` | 同じ `band` の内側には見えて、外には出ない |
| `pub` | `pub let` | `band` の外へ出る |

```yulang
struct point:
    x: int
    y: int
with:
    our p.norm2 = p.x * p.x + p.y * p.y    // companion へ出る
```

- `with:` の method や `act` の operation は、囲んでいる companion module へ出る。ここでは `our` を使う。
- module の外へ出す top-level の helper は `pub` を使う。
- 現状の実装は、`our` と `pub` の差を**アクセス判定だけ**ではほとんど区別していない。上の対応が意図で、実装を合わせる側に倒す。

出典: ユーザー回答（Rust との対応）、`main:web/docs/ja/guide/pitfalls.md`「`our` と `pub` の違い」、`main:notes/design/yulang-language-report.md` §5.2
`pub(crate)` の「crate」に当たる単位は `band`（確定, 2026-11-04）。
素材にあった「`pub` は module 自身の型 pane にも公開する」という記述は、ユーザーも意味を把握していないため**仕様に採らない**（無視してよい, 確定）。

## 2.3 `mod` と test module　〔test module は言語仕様と確定、他は要確認〕

```yulang
mod geometry:
    pub origin = (0, 0)

geometry::origin
```

```yulang
mod helper;        // 同階層の helper.yu（または helper/mod.yu）を子 module として読む
pub mod helper;    // どちらの形にも可視性を付けられる
```

```yulang
mod test named:
    my passing = assert true

mod test:
    my anonymous = assert true
```

- `mod test name:` は名前付き、`mod test:` は無名の test module を作る。通常の実行（`yulang run`）では飛ばされ、
  テスト実行（`yulang test`）では module 内の binding が test として実行される。test module は言語仕様の一部（確定）。
- inline の `mod` は nested module を作る。ファイル形式の `mod name;` は `name.yu` を子 module として読み込む。
- module 内の path は `::` で辿る。

出典: `main:web/docs/ja/reference/modules.md`

## 2.4 `use`　〔基本形は確定、version は未定〕

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

- 上の形（`use path::name`、`as`、`*`、group、`without`、演算子の `(+)` 表記）までを仕様として約束する（確定, 2026-11-04）。
- version 付きの import（`use provider/realm/band::path::name v1.0.0`）は realm / band の方針（2.6）とあわせて後で決める（未定）。
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

## 2.6 配布単位とコード塊の単位　〔方針と名前は確定〕

**配布の単位**と**コードの塊の単位**は別であるべき、という設計（確定, 2026-11-04）。現状の素材では次の用語を使っている。

- `realm` — version を持つ解決空間。配布単位にあたる。
- `band` — realm の中の import / build の島。コード塊の単位にあたる。Rust の crate に近い役割だが、配布の単位ではない。可視性の `our` は band 単位で効く。

```yulang
use realm/helper::answer                      // current realm の別 band
use local/theme/colors::palette v1.0.0        // install 済みの realm
use band::inner::value                        // current band の root から
```

- 通常の module path は current band の中だけを探す。別 band は `realm/` や `local/` で明示する。
- `std::...` は標準ライブラリへの prebound alias。

出典: `main:web/docs/ja/reference/modules.md` §Realm と band の path、`main:spec/2026-06-26-local-realm-band.md`

### 名前

`realm` / `band` の名前は今のまま（確定, 2026-11-04）。
