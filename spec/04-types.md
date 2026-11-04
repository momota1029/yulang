# 章4 型

状態の凡例は [README](README.md)。この章は**表面の型**を扱う。型の形、注釈の書き方、`struct` / `enum` / `type`、一般化。
effect 行の意味（T2・T3）は章5、`role` / `impl` / `where` / `cast` は章6、型の表示は章7 に回す。
素材の effect 行は `;` 区切りで書かれていたが、ここでは新表記の `,` に直してある（[T1](traps.md)）。

## 4.1 基本の型　〔要確認〕

| 型 | 例 | 備考 |
| --- | --- | --- |
| `int` | `0`, `42`, `-7` | 任意精度（章3.1） |
| `float` | `3.14` | |
| `bool` | `true`, `false` | |
| `str` | `"hello"` | |
| `()` | unit | |
| `never` | | 返らない式の型（確定, 2026-11-04） |
| tuple | `(int, str, bool)` | 位置で持つ product |
| list | `list int`, `list 'a` | |
| record | `{x: int, y: int}` | 名前を持つ product（匿名） |
| 関数 | `int -> int` | `->` は右結合 |

- `never` は全ての型の部分型（bottom 型）で、注釈にも書ける（確定, 2026-11-04）。`if` の片側が `never` なら、全体の型はもう片側の型になる。`return` や `last` のような返らない式の型にも現れる。

```yulang
my x: int = if cond: 1 else: fail "oops"    // else 側は never なので int と合う
```

- 要素が 1 つの tuple は末尾に `,` を付けて `(1,)` と書く（確定, 2026-11-04）。`(1)` はグループ化された式で値は `1`。`()` は 0 要素の tuple で unit と同じ。型の `(int,)` も同じ形。

- `(int, int) -> int` は 1 つの tuple を受ける関数の型で、カリー化された `int -> int -> int` とは別の型（確定, 2026-11-04）。`\(a, b) -> ...` は前者になる。

- `xs[i]` は `Index` role を通して解決される（章6）。
- `opt 'a`（`nil` / `just`）と `result 'ok 'err`（`ok` / `err`）は標準ライブラリの enum で、prelude が型と variant の両方を再公開する。

出典: `main:web/docs/ja/reference/types.md`

## 4.2 型変数と注釈　〔注釈の位置は確定、他は要確認〕

型変数は `'a` と書き、注釈の中に直接出す。**型変数を先に宣言する引数リストはない。**

```yulang
my id(x: 'a): 'a = x
```

- `_` は注釈の中で「推論に任せる穴」。型 constructor ではない。
- 注釈の位置は 3 つある。

```yulang
my x: int = 1                  // binding の注釈
my f(x: int): int = x          // 引数と返り値の注釈
([] as list int)               // 式の途中は as
```

- **型注釈は pattern のどこにでも付けられる**（確定, 2026-11-04）。lambda の引数、分割代入の各要素、`case` の arm の pattern も含む（章3b.7）。

```yulang
\(x: int) -> x
my (a: int, b: str) = p
```

- 式の途中の注釈には `as` を使う。`(e : T)` は colon application（`f: x`）と衝突するので使えない。
- 型注釈は**局所的に使い、許す型**であって、effect は注釈を素通りして推論される（[T3](traps.md)）。

出典: `main:web/docs/ja/reference/types.md` §Type variable、§`as` による inline ascription

## 4.3 record　〔幅の部分型付けは確定、他は要確認〕

```yulang
{ x: 3, y: 4 }
{ ..base, x: 3 }          // spread
```

- field access は `.field`。
- spread で field が重複したら、**前に書いたほうが勝つ**（確定, 2026-11-04。JS とは逆）。デフォルト値を後ろに置く形で書ける。

```yulang
my base = { x: 1, y: 2 }
{ x: 3, ..base }          // { x: 3, y: 2 }
{ ..base, x: 3 }          // { x: 1, y: 2 }
```
- **record は幅の部分型付けを持つ**（確定, 2026-11-04）。余分な field を持つ record は、少ない field の型として使える。

```yulang
my get_x(r: {x: int}) = r.x
get_x { x: 1, y: 2 }       // OK: y が余分でも渡せる
```

- 対して `struct`（4.4）は名前で区別される nominal な型で、部分型付けを持たない。
- 型の表示では、省略可能な field は `?` 付きで出る。例: `{width?: 'a} -> 'a | int`。
- record pattern の default（`{ width = 1 }`）が、省略可能な field を生む（章3b.3）。

## 4.4 `struct`　〔`.0` は確定、他は要確認〕

```yulang
struct point { x: int, y: int }
point { x: 3, y: 4 }

struct user_id(int)             // tuple struct
user_id(7)

struct pair 'a 'b { fst: 'a, snd: 'b }    // 型引数
```

- `struct` は**名前で区別される** record 型。値は `point { x: 3, y: 4 }` と作る。
- `struct` の値を作るときは field を全部書く。足りない field はエラー（確定, 2026-11-04）。足りない分を別の値から取るなら spread を使う（`point { x: 3, ..p }`）。
- field に default を宣言できる（`struct point { x: int, y: int = 4 }`）。この場合 constructor が受ける record は `{ x: int, y?: int }` になり、`y` を省略できる。値からは `y` は常に取り出せる（確定, 2026-11-04）。

- 位置の field（tuple struct）と名前の field（record struct）は混在させない（確定, 2026-11-04）。tuple struct は位置だけ（`.0`）、record struct は名前だけ。
- tuple struct は位置で field を持つ。field が 1 個でも constructor と pattern を持ち、括弧を書いても payload の型には変わらない。
- tuple と tuple struct の中身は **`.0`、`.1` で取り出せる**（確定, 2026-11-04）。pattern での分解もできる。

```yulang
struct user_id(int)
my id = user_id(7)
id.0               // 7
(1, 2).0           // 1
```

- パーサ（yu-syntax）は `.0` を読める（2026-11-04）。
- `with:` で companion module に method を足す。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
```

- 構造 projection: `value.(x, y(4))` は tuple、`value.{ first: x }` は record を作る。

出典: `main:web/docs/ja/reference/structs.md`

## 4.5 `enum`　〔constructor のカリー化は確定、他は要確認〕

polymorphic variant の型も存在する（確定, 2026-11-04）。素材にある綴りは `:{A int, B}`。これは `:name payload` の pattern（章3b）に対応する型で、閉じた tag の集合を表す。綴りと意味の細部は要確認。

```yulang
enum opt 'a = nil | just 'a

enum event:
    moved { x: int, y: int }     // record payload
    named { name: str }
```

- variant は companion module の member（`event::moved`）。
- **複数の payload を持つ variant の constructor は、カリー化された関数**（確定, 2026-11-04）。部分適用ができ、値としても取り出せる。

```yulang
enum tree 'a:
    leaf
    node 'a (tree 'a) (tree 'a)

tree::node : 'a -> tree 'a -> tree 'a -> tree 'a
my f = tree::node 1            // 部分適用。残りの 2 つを取る関数
```
- variant の payload には、位置の型と record の両方が書ける。
- `error` の variant に record payload を書くことは、パーサは受理するが checker が拒否する。
  **許す**（確定, 2026-11-04）。いまの checker の拒否は実装の穴として扱う。例:

```yulang
error path_err:
    not_found { path: str, hint: str }     // 許す。いまの実装は unsupported syntax で拒否する
```

出典: `main:web/docs/ja/reference/structs.md` §Variant の record payload

## 4.6 `type`　〔確定〕

`type` の宣言には 2 つの形がある（確定, 2026-11-04）。

```yulang
type meters = int                        // alias: meters は int の別名
```

```yulang
type list 'a                             // 名前だけの nominal 型
type ref 'e 'a with:                     // companion を伴う nominal 型
    struct self:
        get: () -> ['e] 'a
```

- `type T = ...` は **alias**（別名）。新しい型は作らない。
- `type T ... with:` + `struct self { ... }` の形は、**nominal な型**と companion module を作る。
  `struct self` が、その型の中身（field）を宣言する。`=` の alias とは別物なので注意。
- 標準ライブラリの `list` / `str` / `ref` も companion module に method を定義している。

注意: 同じ `type` で、`=` があれば alias、`with:` があれば nominal、と綴りで意味が変わる。

## 4.7 一般化と値制限　〔確定〕

`binding` の右辺が**構文上の値**であるときだけ一般化する（確定, 2026-11-04）。関数値には多相の型が付く。

```yulang
my id = \x -> x
(id 1, id "text")           // OK: id は多相

my id2 = (\f -> f) (\x -> x)   // 右辺が計算: 一般化しない（単相）
```

- 再帰する関数の binding は、許される強連結成分（SCC）を作る。
- 値の cycle は拒否される。

```yulang
my make x = x
my a = make b
my b = make a              // エラー: 再帰する component の中で computed value を取得している
```

出典: `main:web/docs/ja/reference/types.md` §Value restriction、`main:spec/2026-06-13-computed-fetch-value-restriction.md`

## 4.8 書けない型と、表示に出る型　〔要確認〕

- 推論結果には union / intersection（`'a | int`、`'a & {width?: ⊤}`）が出ることがある。
  これらを**注釈として直接書く安定した構文はない**。
- 注釈を足すと、表示型を意図した公開形に絞れる。表示の規則は章7。

## 確認してほしい点

- **G5'** polymorphic variant の型の綴り（`:{A int, B}`）が現行のものか。payload を持つ tag と持たない tag の書き分け。
