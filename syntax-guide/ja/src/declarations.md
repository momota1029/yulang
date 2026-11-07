# 宣言と可視性

この章は、名前を作る書き方(`my` / `our` / `pub`)、module(`mod`)、名前を持ち込む書き方(`use`)を見る。
評価の順序や、値制限の細かい規則は `spec/02-declarations.md` に任せて、ここでは「どう読まれるか」を並べる。

## binding

```yulang
my x = 1
our answer = 42
pub exported = answer
```

状態: 仮採用・パース検査済み。出典: `spec/02-declarations.md` 2.1。

関数の引数は、binding の頭部に直接書ける。これは**カリー化された lambda の糖衣**。

```yulang
my add x y = x + y
// 同じ意味:
my add = \x -> \y -> x + y
```

状態: 確定・パース検査済み。

### 再帰と再束縛

```yulang
my fact n =
    if n == 0: 1
    else: n * fact (n - 1)     // 引数のある binding は、自分を呼べる

my a = 1
my a = a + 1                    // 右辺の a は 1 行目の a。結果は 2
```

- 引数のある binding(関数)は、自分自身を呼べる。引数のない値の binding は自分を指せず、右辺の同名は、既にある束縛を指す。
- 同じ scope で同名の `my` を書くのは許され、後のものが前のものを隠す。
- `our` / `pub` の同名 binding を、同じ module に 2 つ書くとエラーになる。外から見える名前は 1 module に 1 つだけ。

状態: 確定・パース検査済み。出典: `spec/02-declarations.md` 2.1。

### 参照の順序

関数、lambda、literal のように評価が要らない binding は、書く順番に関係なく互いを参照できる(相互再帰もできる)。
関数の適用を含む式のように評価が要る binding は、上から順に評価される。

```yulang
my even n = if n == 0: true else: odd (n - 1)     // odd は下にあるが参照できる
my odd n = if n == 0: false else: even (n - 1)

my a = b + 1     // OK: b は literal なので下にあってもよい
my b = 2
```

評価が要る binding どうしを逆順に置くとエラーになる。詳しい規則(判定が保守的であること、`\ys -> map h ys` のように lambda で包むと外れること)は、`spec/02-declarations.md` 2.1 を見る。

### method を定義する binding

名前に dot を含む binding は、method の定義になる。

```yulang
our x.tap f = f x; x                   // どの型にも付く method
our p.norm2 = p.x * p.x + p.y * p.y    // トップレベルに書いても method になる
```

書ける場所は、`with:` の中に限らない。module のトップレベル、`role` や `act` の中にも書ける。
状態: 確定・パース検査済み。

## 可視性: `my` / `our` / `pub`

| 語 | Rust での対応 | 見える範囲 |
| --- | --- | --- |
| `my` | `let` | その module の中だけ(private)。local binding は字句的な local |
| `our` | `pub(crate) let` | 同じ `band` の内側には見えて、外には出ない |
| `pub` | `pub let` | `band` の外へ出る |

`band` は、コードの塊の単位(Rust の crate に近い役割)。配布の単位(`realm`)とは別の概念。この章では、これ以上は扱わない。

```yulang
struct point:
    x: int
    y: int
with:
    our p.norm2 = p.x * p.x + p.y * p.y    // companion へ出る
```

- `with:` の method や `act` の operation は、囲んでいる companion module へ出る。ここでは `our` を使う。
- module の外へ出す top-level の helper は `pub` を使う。

状態: 確定・パース検査済み。出典: `spec/02-declarations.md` 2.2。

## `mod`

```yulang
mod geometry:
    pub origin = (0, 0)

geometry::origin
```

inline の `mod` は、nested module を作る。module の中の名前は `::` で辿る。

```yulang
mod helper;        // 同階層の helper.yu(または helper/mod.yu)を子 module として読む
pub mod helper;    // どちらの形にも可視性を付けられる
```

ファイル形式の `mod name;` は、`name.yu` または `name/mod.yu` を子 module として読み込む。両方あればエラー。

### 子と親の見え方

```yulang
my secret = 1

mod inner:
    pub get = secret      // 親の my を参照できる
```

子 module は字句的に親の内側にあるので、親の `my` を参照できる。逆に、親から子の `my` は見えない(`inner::hidden` のように子の `my` を指すとエラー)。

### test module

```yulang
mod test named:
    my passing = assert true

mod test:
    my anonymous = assert true
```

`mod test name:` は名前付き、`mod test:` は無名の test module。通常の実行では飛ばされ、テスト実行で、module 内の binding が test として動く。

状態: test module は確定。それ以外は仮採用。パース検査済み。出典: `spec/02-declarations.md` 2.3。

## `use`

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

状態: 確定・パース検査済み。出典: `spec/02-declarations.md` 2.4。

### 持ち込んだ名前は、その module の中だけ

`use` で入れた名前は、その module の中だけで効く。外から `a::map` のように辿ることはできない。外へ出すには、可視性を付ける。

```yulang
use std::data::list::map          // この module の中だけ
our use std::data::list::map      // 同じ band の中へ再公開
pub use std::data::list::map      // band の外へ再公開
```

### 名前がぶつかったとき

```yulang
use std::data::list::*
my map f xs = ...                 // glob の map より、自分の map が勝つ
```

- glob(`use path::*`)で入れた名前と、自分の定義がぶつかったら、自分の定義が勝つ。
- 名前を指定した `use path::name` と、自分の定義がぶつかったらエラー。`as` で別名にするか、片方を消す。
- 2 つの glob が同じ名前を持ち込んだときは、`use` した時点ではエラーにならない。その名前を実際に使ったときだけ、曖昧エラーになる。

状態: 確定。

### 演算子と prelude

演算子の宣言は、`use` で import したファイルだけで読める([演算子は宣言で決まる](operators.md))。
通常の entry file には、`use std::prelude::*` が暗黙に付く。

### version 付きの import

`use provider/realm/band::path::name v1.0.0` のような、version を持つ import の書き方は、まだ決まっていない(未定)。

## companion module

`struct`、`type ... with:`、`enum`、`act`、`error`、`role` は、**同名の companion module** を作る。
body の中の `our` / `pub` は、そこへ入る。

```yulang
opt::just 1
out::write "hi"
```

同名の `mod` を自分で書くと、companion module に**合流**する。`with:` で足したものと同じ場所に入る。

```yulang
struct point { x: int, y: int }

mod point:
    pub origin = point { x: 0, y: 0 }     // point::origin が companion に足される
```

合流した結果、同じ名前が 2 つできたら、重複定義のエラー。
prelude が `just` / `nil` / `ok` / `err` のような標準の variant を再公開するので、通常は修飾なしで書ける。

状態: 仮採用・パース検査済み。出典: `spec/02-declarations.md` 2.5。
