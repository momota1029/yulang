# 値と型

Yulang が扱う基本の値の形（primitive、tuple、record、list、optional、result、range）と、その上に乗る関数型・effect row・type variable・role constraint・推論で表示される union/intersection を概観する。

## Primitive types

| Type | 例 |
|------|----|
| `int` | `0`, `42`, `-7` |
| `float` | `3.14`, `-0.5` |
| `bool` | `true`, `false` |
| `str` | `"hello"` |
| `()` | unit value |
| `never` | 返らない式の型 |

## Tuple

```yulang
(1, "hello", true)
```

tuple は位置で持つ product。`my (a, b, c) = triple` のように pattern で分解できる。

## List

```yulang
[1, 2, 3]
```

`'a` の list は `list 'a`。`xs[i]` は `Index` role を通して解決される。

## Record

```yulang
{ x: 3, y: 4 }
{ ..base, x: 3 }
{ x: 3, ..rest }
```

anonymous な named product である。field access は `.field`。

record pattern は default によって field を省略可能にできる。

```yulang
my width_or_default { width = 1 } = width
my keep_rest { ..rest, width = 1 } = rest
```

型表示では、省略可能な record field は `?` 付きで出る。たとえば `{width?: α} -> α | int` のような形である。残り field を保持する spread pattern では、`α & {width?: ⊤}` のような intersection が表示されることがある。

## Optional

```yulang
just 42
nil
```

`opt 'a` は標準ライブラリの `enum opt 'a = nil | just 'a` である。prelude は type と variant の両方を reexport するため、通常のコードでは `std::data::opt::` や `opt::` を付けずに `opt`、`just`、`nil` と書く。

## Result

```yulang
ok 1
err "bad"
```

`result 'ok 'err` は fallible computation を値として返すための標準型。prelude は `result`、`ok`、`err` を reexport するため、local name と衝突する場合だけ修飾する。

## Range

```yulang
0..<10  // 0 から 9
0..10   // 0 から 10
0..     // 0 から無限
```

range は `Fold` を実装するので、`for x in r:` や `each r` に渡せる。

## Type variable

type variable は `'a` のように書き、型注釈の中へ直接出す。普通の関数 binding では、型変数だけを先に宣言する引数リストはない。

```yulang
my id(x: 'a): 'a = x
```

多くの場合、型推論が type variable を埋める。注釈は曖昧さを減らしたり、公開 API を読みやすくしたりするために使う。

## `as` による inline ascription

binding ascription (`my x: T = e`) や引数 ascription (`my f(x: T) = ...`) は
`:` を使うが、式の途中で部分式に型を当てたいときは `as` を使う。

```yulang
([] as list int)
(nil as opt str)
my n = (read_input() as int) + 1
```

inline の `:` は colon application (`f: x`) に予約されているので、式位置の
`(e : T)` を許すと衝突する。多相値の型を `my` binding を立てずにその場で
固定したいときは `as` を使う。

## 関数型と effectful computation

```yulang
int -> int
() -> [console] str
[console] str
```

`A -> B` は関数型である。返り値側で effect を起こす関数は、返り値側に effect row を持つ。

```yulang
() -> [console] str
```

`[console] str` だけで書いた型は、`console` effect を起こす可能性があり、`str` を返す computation value を表す。handler や control abstraction の引数でよく使う。

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
```

型表示では `α [io; β] -> [β] α` のように、関数の引数側にも effect row が出ることがある。これは「引数が effectful computation である」という意味である。source annotation では、`x: [io; 'e] 'a` のように具体的な値型か type variable を置く。

`_` は annotation 内で推論に穴埋めを任せる placeholder として使えるが、型そのものではない。

## Effect row

```yulang
[console; 'e] str
() -> [console; 'e] str
```

row は named effect の列と、任意の残りを表す row variable `; 'e` を持てる。`[_]` のような wildcard row は annotation placeholder であり、effect row type そのものの標準形ではない。

## Role constraint

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

`where` は type variable が role を実装していることを要求する。

## 推論された union / intersection

Yulang の推論結果には、union や intersection が表示されることがある。ただし、それらを source annotation として直接書くための安定した構文はまだない。

```text
α | int
α & {width?: ⊤}
```

branch、default value、pattern spread などで複数の形が残ると、Types pane にこのような型が出る。公開 API では注釈を足すと、意図した形に収束させやすくなる。

## 関連

- [エフェクト](./effects) — effect の宣言、呼び出し、handler。
- [型推論の理論](./type-theory) — subtyping、effect row、handler hygiene の内部的な見方。
