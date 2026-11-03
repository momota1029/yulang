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
| `never` | | 返らない式の型 |
| tuple | `(int, str, bool)` | 位置で持つ product |
| list | `list int`, `list 'a` | |
| record | `{x: int, y: int}` | 名前を持つ product（匿名） |
| 関数 | `int -> int` | `->` は右結合 |

- `xs[i]` は `Index` role を通して解決される（章6）。
- `opt 'a`（`nil` / `just`）と `result 'ok 'err`（`ok` / `err`）は標準ライブラリの enum で、prelude が型と variant の両方を再公開する。

出典: `main:web/docs/ja/reference/types.md`

## 4.2 型変数と注釈　〔要確認〕

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

- 式の途中の注釈には `as` を使う。`(e : T)` は colon application（`f: x`）と衝突するので使えない。
- 型注釈は**局所的に使い、許す型**であって、effect は注釈を素通りして推論される（[T3](traps.md)）。

出典: `main:web/docs/ja/reference/types.md` §Type variable、§`as` による inline ascription

## 4.3 record　〔要確認〕

```yulang
{ x: 3, y: 4 }
{ ..base, x: 3 }          // spread
```

- field access は `.field`。
- 型の表示では、省略可能な field は `?` 付きで出る。例: `{width?: 'a} -> 'a | int`。
- record pattern の default（`{ width = 1 }`）が、省略可能な field を生む（章3b.3）。

## 4.4 `struct`　〔要確認〕

```yulang
struct point { x: int, y: int }
point { x: 3, y: 4 }

struct user_id(int)             // tuple struct
user_id(7)

struct pair 'a 'b { fst: 'a, snd: 'b }    // 型引数
```

- `struct` は**名前で区別される** record 型。値は `point { x: 3, y: 4 }` と作る。
- tuple struct は位置で field を持つ。field が 1 個でも constructor と pattern を持ち、括弧を書いても payload の型には変わらない。
- `with:` で companion module に method を足す。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
```

- 構造 projection: `value.(x, y(4))` は tuple、`value.{ first: x }` は record を作る。

出典: `main:web/docs/ja/reference/structs.md`

## 4.5 `enum`　〔要確認〕

```yulang
enum opt 'a = nil | just 'a

enum event:
    moved { x: int, y: int }     // record payload
    named { name: str }
```

- variant は companion module の member（`event::moved`）。
- variant の payload には、位置の型と record の両方が書ける。
- `error` の variant に record payload を書くことは、パーサは受理するが checker が拒否する（確認 G5）。

出典: `main:web/docs/ja/reference/structs.md` §Variant の record payload

## 4.6 `type`　〔要確認・素材が古い〕

```yulang
type list 'a                            // 名前だけの nominal 型
type ref 'e 'a with:                    // companion を伴う型
    struct self:
        get: () -> ['e] 'a
```

- `type` は nominal な型と companion module を作る。
- `type T = ...` が **alias なのか別の意味なのか**は、素材が古く不明（確認 G1）。

## 4.7 一般化と値制限　〔要確認〕

`binding` の右辺が**構文上の値**であるときだけ一般化する。関数値には多相の型が付く。

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

- **G1** `type T = ...` は何か。alias か、別の型を作るのか。
- **G2** 値制限（右辺が構文上の値のときだけ一般化）は、仕様として約束してよいか。
- **G3** `never` は「返らない式」の型でよいか。`bottom` との関係。
- **G4** `error` の variant に record payload が書けないのは、仕様か実装の穴か。
- **G5** 型を表す構文として、polymorphic variant の型（`:{A int, B}`）が素材にあるが、現行の言語にあるか。
