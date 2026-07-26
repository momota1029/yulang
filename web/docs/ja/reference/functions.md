# 関数

関数 binding、カリー化された呼び出し形式、ラムダ、型注釈と effect 注釈をまとめる。
record pattern 引数、method、role constraint も扱う。

## 宣言

```yulang
my add x y = x + y
our greet name = "hello, " + name
pub double x = x + x
```

binding の左辺は pattern である。pattern が直接の名前のとき、その後ろに続く pattern
が関数引数になる。

| キーワード | 公開範囲 |
|---|---|
| `my` | 現在の module / block で private |
| `our` | 囲んでいる companion から見える（method の標準形）|
| `pub` | module 境界をまたいで export される |

## 引数とカリー化

```yulang
my add x y = x + y
my add' = \x -> \y -> x + y
```

複数引数の binding は左から右にカリー化される。`add 1` は `y` を待つ関数である。
裸 application（`add 1 2`）でも C 風（`add(1, 2)`）でも呼べる。両方とも
内部はカリー化された application に lower される。

```yulang
my inc = add 1
inc 41                 // 42
```

## 呼び出しの形

```yulang
add 1 2                // 裸 application
add(1, 2)              // C 風呼び出し
add: 1                 // colon application（2 引数関数では稀）
```

裸 application が標準形である。視覚的に引数をまとめたいときや、裸だと token が
流れて読みづらいときに C 風を使う。

## ラムダ

```yulang
\x -> x + 1
\x y -> x + y
```

ラムダは `\` で始まる。複数引数のラムダ `\x y -> ...` は binding の頭と同じく
カリー化される。

ラムダの引数自体も pattern である。

```yulang
\(x, y) -> x + y
\{ name } -> "hello, " + name
```

## 型注釈

```yulang
my double(x: int): int = x + x
my mark(label: str, value: 'a): 'a = value
```

引数と戻り型の注釈は任意である。省略すると推論が埋める。API 境界のドキュメント、
そのままだと開いてしまう generic の固定、曖昧さの解消、のいずれかに使う。

## effect 付きの注釈

```yulang
my ask(): [console] str = console::read()
my run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console (k "42")
```

戻り型の角括弧形は effect row である。`[console] str` は「`str` を返し、`console`
effect を要求する」という意味。`[console; 'e] 'a` のように tail 変数を入れる
と他の effect も開いたままになる。

## オプショナル引数としてのレコードパターン

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area { width: 3, height: 4 }
area {}
```

デフォルト付きのレコードパターンは、呼び出し側で各 field を省略可能にする。
デフォルトは左から右へ評価され、後ろのデフォルトは前の field を参照できる。

```yulang
my f {a = 1, b = a + 1} = (a, b)
```

## `with:` 経由の method

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

`with:` 内の `our recv.name args = body` で、`value.name args` で呼べる
method を定義する。レシーバ `recv` は単なる名前 — 読みやすい名前を選ぶ。

## role の method

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y
```

role の method ヘッダーは `with:` と同じレシーバ形を使う。`:` の後ろは
レシーバを当てた後の関数型 — `Add` なら `a.add` は相手側の引数を取る関数。

## where 句

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

`where 'a: Role` は binding の型変数に role 制約を追加する。binding の推論型
にその制約が伝播するので、`twice 1` の呼び出しは `Add int` を要求する。

`where` 句は role 本体や impl 本体にも書ける。role 本体に書くと各 method に
継承される。impl 本体に書くと、その impl 候補の前提条件になる。

## ファイルの検査

```bash
yulang check examples/showcase.yu
# repo から動かす場合
cargo run -q -p yulang -- check examples/showcase.yu
```

`check` は file を検査する。
成功時は何も出力せず、失敗時だけ diagnostic を出す。
compiler IR には、推論された binding 型が含まれる。
residual な型変数（`α`、`β`、…）と role 制約（`Add<α> => ...`）も含まれる。
`yulang dump examples/showcase.yu --poly` で確認できる。

## 関連ページ

- [パターン](./patterns) — `my` / ラムダ / 引数で共通の pattern 文法
- [構造体とロール](./structs) — companion method と role impl
- [エフェクト](./effects) — 引数 / 戻り型での effect row
- [クックブック](../guide/cookbook) — これらを組み合わせるレシピ
