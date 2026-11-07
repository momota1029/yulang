# 型の書き方

この章は、型の注釈の書き方と、型を作る宣言(`struct` / `enum` / `type`)を見る。部分型の細かい規則や、推論の内部は `spec/04-types.md` と、その先の核の計算体系に任せる。
型の名前も、値の名前と同じように小文字で書く。型変数は `'a` のように `'` で始める。

## 基本の型

| 型 | 例 | 備考 |
| --- | --- | --- |
| `int` | `0`, `42`, `-7` | 任意精度 |
| `float` | `3.14` | |
| `bool` | `true`, `false` | |
| `str` | `"hello"` | |
| `()` | unit | |
| `never` | | 返らない式の型。全ての型の部分型 |
| `any` | | 最大の型。どんな値も受けるが、受けた値は何にも使えない |
| tuple | `(int, str, bool)` | 位置で持つ product |
| list | `list int`, `list 'a` | |
| record | `{x: int, y: int}` | 名前を持つ product(匿名) |
| 関数 | `int -> int` | `->` は右結合 |

- `any` は TypeScript の `unknown` と同じで、`any` 型の値は何にも使えない。TypeScript の `any`(型検査を抜ける穴)とは別物。
- `never` は、`if` の片側が返らないときに効く。

```yulang
my x: int = if cond: 1 else: fail "oops"    // else 側は never なので int と合う
```

- 要素が 1 つの tuple は、末尾に `,` を付けて `(1,)` と書く。`(1)` はグループ化された式で、値は `1`。`()` は 0 要素の tuple で、unit と同じ。
- `(int, int) -> int` は 1 つの tuple を受ける関数の型で、カリー化された `int -> int -> int` とは別の型。`\(a, b) -> ...` は前者になる。
- `opt 'a`(`nil` / `just`)と `result 'ok 'err`(`ok` / `err`)は標準ライブラリの enum。

状態: 仮採用(`never` と `any` は確定)。出典: `spec/04-types.md` 4.1。

## 型変数と注釈

型変数は `'a` と書き、注釈の中に直接出す。**型変数を先に宣言する引数リストは無い**。

```yulang
my id(x: 'a): 'a = x
```

`_` は、注釈の中で「推論に任せる穴」。

### 注釈を付ける 3 つの位置

```yulang
my x: int = 1                  // binding の注釈
my f(x: int): int = x          // 引数と返り値の注釈
([] as list int)               // 式の途中は as
```

- 式の途中の注釈には `as` を使う。`(e : T)` は colon application(`f: x`)と衝突するので使えない。
- 型の注釈は pattern のどこにでも付けられる。lambda の引数、分割代入の各要素、`case` の arm の pattern も含む。

```yulang
\(x: int) -> x
my (a: int, b: str) = p
```

### 注釈は公開される型を決める

値の型の注釈は、**公開される型**を決める。推論された型が注釈に収まることを検査して、公開型は注釈の型になる。戻り値の注釈で本体より狭くすれば、公開型から情報が減る。

```yulang
my f(): {x: int} = {x: 1, y: 2}     // 本体は {x: int, y: int}。公開型は () -> {x: int}
my g(n: int) = n + 1                // 公開型は int -> int
```

effect の行は例外で、注釈は検査だけを行い、行の変数を束縛しない(spec の章5)。
状態: 注釈の位置は確定・パース検査済み。出典: `spec/04-types.md` 4.2。

## record

```yulang
{ x: 3, y: 4 }
{ ..base, x: 3 }          // spread
```

- field は `.field` で読む。
- spread で field が重複したら、**前に書いたほうが勝つ**(JS とは逆)。デフォルト値を後ろに置く形で書ける。

```yulang
my base = { x: 1, y: 2 }
{ x: 3, ..base }          // { x: 3, y: 2 }
{ ..base, x: 3 }          // { x: 1, y: 2 }
```

- **record は幅の部分型付けを持つ**。余分な field を持つ record は、少ない field の型として使える。

```yulang
my get_x(r: {x: int}) = r.x
get_x { x: 1, y: 2 }       // OK: y が余分でも渡せる
```

- 隠れた field の式も評価される。`{ x: log 1, x: log 2 }` は `log 1`、`log 2` の順に評価され、結果は `{ x: 1 }` になる。
- 型の表示では、省略可能な field が `?` 付きで出る(`{width?: 'a} -> 'a | int`)。record pattern の default(`{ width = 1 }`)が、省略可能な field を生む。

状態: 幅の部分型付けは確定・パース検査済み。出典: `spec/04-types.md` 4.3。

## `struct`

```yulang
struct point { x: int, y: int }
point { x: 3, y: 4 }

struct user_id(int)             // tuple struct
user_id(7)

struct pair 'a 'b { fst: 'a, snd: 'b }    // 型引数
```

- `struct` は、**名前で区別される** record 型。部分型付けは持たない(record と違う)。
- 値を作るときは、field を全部書く。足りない分を別の値から取るなら、spread を使う(`point { x: 3, ..p }`)。
- field に default を宣言できる(`struct point { x: int, y: int = 4 }`)。constructor が受ける record は `{ x: int, y?: int }` になり、`y` を省略できる。
- 位置の field(tuple struct)と名前の field(record struct)は、混在させない。
- tuple と tuple struct の中身は、`.0`、`.1` で取り出せる。

```yulang
struct user_id(int)
my id = user_id(7)
id.0               // 7
(1, 2).0           // 1
```

### `with:` で method を足す

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
```

### 構造 projection

同じ値から複数の field を取り出す略記。

```yulang
value.(x, y(4))          // (value.x, value.y(4)) という tuple
value.{ first: x }       // {first: value.x} という record
```

状態: `.0` は確定。他は仮採用。パース検査済み。出典: `spec/04-types.md` 4.4。

## `enum`

```yulang
enum opt 'a = nil | just 'a

enum event:
    moved { x: int, y: int }     // record payload
    named { name: str }
```

- variant は companion module の member(`event::moved`)。修飾なしで使うには、`color::red` と書くか、`use color::*` で入れる。prelude が再公開する `just` / `nil` / `ok` / `err` だけが、はじめから修飾なしで使える。
- variant の payload には、位置の型と record の両方が書ける。
- **複数の payload を持つ variant の constructor は、カリー化された関数**。部分適用ができ、値としても取り出せる。

```yulang
enum tree 'a:
    leaf
    node 'a (tree 'a) (tree 'a)

// tree::node の型: 'a -> tree 'a -> tree 'a -> tree 'a
my f = tree::node 1            // 部分適用。残りの 2 つを取る関数
```

状態: constructor のカリー化は確定。他は仮採用。パース検査済み。出典: `spec/04-types.md` 4.5。

### polymorphic variant の型

`:name payload` の pattern に対応する型で、閉じた tag の集合を表す。綴りは 2 つあり、同じ意味。

```yulang
my f(x: :{ready, some int}) = ...         // { } に tag を並べる形
my g(x: :ready | :some int) = ...         // tag ごとに : を付けて | でつなぐ形
```

payload が無ければ unit。tag は一意で、payload は tag ごとに合流する(`if b then :id 1 else :id "a"` の型は `:id (int | str)`)。
variant の「残り」は推論される。行の変数 `'r` は、利用者が注釈に書かない。注釈に書けるのは、閉じた `:str str | :num int` の形だけ。

## `type`

`type` の宣言には 2 つの形がある。

```yulang
type meters = int                        // alias: meters は int の別名
```

```yulang
type list 'a                             // 名前だけの nominal 型
type ref 'e 'a with:                     // companion を伴う nominal 型
    struct self:
        get: () -> ['e] 'a
```

- `type T = ...` は **alias**(別名)。新しい型は作らない。
- `type T ... with:` と `struct self { ... }` の形は、**nominal な型**と companion module を作る。`struct self` が、その型の中身(field)を宣言する。

同じ `type` でも、`=` があれば alias、`with:` があれば nominal、と綴りで意味が変わる。
状態: 確定・パース検査済み。出典: `spec/04-types.md` 4.6。

## 一般化と値制限

binding の右辺が**構文上の値**であるときだけ、型を一般化する。関数値には多相の型が付く。

```yulang
my id = \x -> x
(id 1, id "text")           // OK: id は多相

my id2 = (\f -> f) (\x -> x)   // 右辺が計算: 一般化しない(単相)
```

### 再帰と注釈

再帰する binding の集まり(SCC)の中では、型は単相で連立して解く。**全ての引数と戻り値の型が書かれた** binding だけは、注釈のスキームを仮定でき、再帰呼び出しのたびに型変数を別の型で使える(多相再帰)。

```yulang
my depth(x: 'a, n: int): int =
    if n == 0: 1
    else: depth((x, x), n - 1) + 1        // 注釈があるので 'a を変えて呼べる
```

「全部書かれた」は、型が全部書かれているかだけで決まる。`_` の穴や、注釈の無い引数があれば、その binding は単相。effect の行は数えない。

### 値の cycle

```yulang
my make x = x
my a = make b
my b = make a              // エラー: 再帰する component の中で、計算を取得している
```

状態: 確定・パース検査済み。出典: `spec/04-types.md` 4.7。

## 注釈に書けない型

推論の結果には、union や intersection(`'a | int`、`'a & {width?: any}`)が出ることがある。これらを**注釈として直接書くことはできない**。
注釈に書ける型は、nominal な型・tuple・record・関数・型変数・`:{...}` だけ。値を複数の型から選びたいときは、`enum` を作る。
`:ready | :some int` の `|` は、polymorphic variant の型の綴りで、一般の union 型を書く構文ではない。
状態: 仮採用。出典: `spec/04-types.md` 4.8。
