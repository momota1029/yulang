# チートシート

Yulang の構文を 1 ページで眺めるためのページです。各節は思い出し用なので、詳細はリファレンスを参照してください。

## binding

```yulang
my x = 1                       // 私的
our exposed = 2                // companion から見える
pub exported = 3               // 外部 export

my add x y = x + y             // 引数は名前のあとに並べる
my (a, b) = (1, 2)             // 分割代入
\x -> x + 1                    // ラムダ
\x y -> x + y                  // curry されたラムダ
```

## application の形

```yulang
f x y                          // 裸の application
f(x, y)                        // C 風呼び出し（内部は curry）
f: x                           // colon application
f.method                       // ドット選択（続けて引数を書けば application）
xs[0]                          // インデックス
```

空白は意味を持ちます。`f(x)` は呼び出し、`f (x)` は `f` を `(x)` に裸 application、`f: x` は colon、`f :x` は `f` をシンボル `:x` に裸 application、とそれぞれ別物です。

## ブロックと layout

```yulang
{ my x = 1; x + 1 }            // brace block
my big =
    my x = 1                   // 字下げで binding 本体が続く
    x + 1
```

`:` は statement 的な形の末尾で layout block を開きます。

## 条件分岐

```yulang
if cond: a else: b
if cond { a } else { b }

case value:
    0 -> "zero"
    x if x > 0 -> "positive"
    _ -> "other"
```

## ループと早期脱出

```yulang
for x in 0..10:        // 11 回反復: 0..10 は閉区間 (半開は 0..<10)
    say x

for x in xs:
    if pred x: last
    else: next

sub:
    for x in xs:
        if x == target: return x
        else: ()
    default
```

## データ型

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

enum opt 'a = nil | just 'a

type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
```

## パターン

```yulang
case v:
    0 -> ...                   // リテラル
    x -> ...                   // bind
    _ -> ...                   // ワイルドカード
    (a, b) -> ...              // タプル
    { x, y = 1 } -> ...        // デフォルト付きレコード
    [head, ..tail] -> ...      // リスト spread
    just x -> ...              // enum variant（prelude）
    color::red -> ...          // enum variant（修飾）
```

## エフェクト

```yulang
act log:
    pub put: str -> ()

catch action:
    log::put msg, k -> k ()
    v -> v
```

関数型は effect row を持ちます: `str -> [fs; e] str`。

## エラー

```yulang
error fs_err:
    not_found str
    denied str

fail fs_err::not_found "x"

catch read_or_throw:
    fs_err::not_found p, _ -> recover p
    v -> v

fs_err::wrap: read_or_throw
```

## 参照

```yulang
my $count = 0
&count = $count + 1
$count
```

## role と impl

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y

my twice x = x.add x           // 推論: Add<α> => α -> α
```

## 演算子

```yulang
pub prefix(not) 8.0.0 = std::bool::not
pub infix (+) 5.0.0 5.0.0 = \x -> \y -> x.add y
pub suffix (..) 8.0.0 = std::range::from_included
pub lazy infix(or) 1.0.0 1.0.0 = \a -> \b -> if a(): true else: b()
```

## モジュールと import

```yulang
use std::undet::*
use std::list::{map, filter}
use std::ops::* without (+), debug
```

## コメント

```yulang
// 行コメント
/* ブロックコメント */
-- 単一行 doc コメント
---
複数行 doc コメント
---
```

## 推論結果を表示

```bash
yulang check examples/showcase.yu
# repo から動かす場合
cargo run -q -p yulang -- check examples/showcase.yu
```

## 関連ページ

- [ツアー](./tour) — 物語仕立てで一通り
- [クックブック](./cookbook) — タスク指向のレシピ
- [リファレンス](../reference/) — 言語の正式リファレンス
- [イディオム](../reference/idioms) — Yulang らしい書き方
