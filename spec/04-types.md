# 章4 型

状態の凡例は [README](README.md)。この章は**表面の型**を扱う。型の形、注釈の書き方、`struct` / `enum` / `type`、一般化。
effect 行の意味（T2・T3）は章5、`role` / `impl` / `where` / `cast` は章6、型の表示は章7 に回す。
素材の effect 行は `;` 区切りで書かれていたが、ここでは新表記の `,` に直してある（[T1](traps.md)）。

## 4.1 基本の型　〔仮採用〕

| 型 | 例 | 備考 |
| --- | --- | --- |
| `int` | `0`, `42`, `-7` | 任意精度（章3.1） |
| `float` | `3.14` | |
| `bool` | `true`, `false` | |
| `str` | `"hello"` | |
| `()` | unit | |
| `never` | | 返らない式の型（確定, 2026-11-04） |
| `any` | | 最大の型（確定, 2026-11-06）。どんな値も受けられるが、受けた値は何にも使えない |
| tuple | `(int, str, bool)` | 位置で持つ product |
| list | `list int`, `list 'a` | |
| record | `{x: int, y: int}` | 名前を持つ product（匿名） |
| 関数 | `int -> int` | `->` は右結合 |

- `never` は全ての型の部分型（bottom 型）で、注釈にも書ける（確定, 2026-11-04）。`if` の片側が `never` なら、全体の型はもう片側の型になる。`return` や `last` のような返らない式の型にも現れる。
- **`any` は全ての型の上位型（top 型）で、注釈にも書ける**（確定, 2026-11-06）。TypeScript の `unknown` と同じで、`any` 型の値は何にも使えない。TypeScript の `any`（型検査を抜ける穴）とは別物なので注意。推論で負の位置に残った未知の型は `any` になる。junction の `all` / `any`（章3c）は値の名前で、型の `any` とは名前空間が別である。

```yulang
my x: int = if cond: 1 else: fail "oops"    // else 側は never なので int と合う
```

- 要素が 1 つの tuple は末尾に `,` を付けて `(1,)` と書く（確定, 2026-11-04）。`(1)` はグループ化された式で値は `1`。`()` は 0 要素の tuple で unit と同じ。型の `(int,)` も同じ形。

- `(int, int) -> int` は 1 つの tuple を受ける関数の型で、カリー化された `int -> int -> int` とは別の型（確定, 2026-11-04）。`\(a, b) -> ...` は前者になる。

- `xs[i]` は `Index` role を通して解決される（章6）。
- `opt 'a`（`nil` / `just`）と `result 'ok 'err`（`ok` / `err`）は標準ライブラリの enum で、prelude が型と variant の両方を再公開する。

出典: `main:web/docs/ja/reference/types.md`

## 4.2 型変数と注釈　〔注釈の位置は確定、他は仮採用〕

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
- **値の型の注釈は、公開される型を決める**（確定, 2026-11-06）。推論された型が注釈に収まること（推論結果 ≤ 注釈）を検査し、公開型は注釈の型になる。戻り値の注釈で本体より狭くすれば、公開型から情報が減る。引数の注釈も公開される引数の型を決める。effect の行は例外で、注釈は検査だけを行い、行変数を束縛しない（章5.5・5.5b）。

```yulang
my f(): {x: int} = {x: 1, y: 2}     // 本体は {x: int, y: int}。公開型は () -> {x: int}
my g(n: int) = n + 1                // 公開型は int -> int
```


出典: `main:web/docs/ja/reference/types.md` §Type variable、§`as` による inline ascription

## 4.3 record　〔幅の部分型付けは確定、他は仮採用〕

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

- **record の型は、意味が等しければ同じ型である**（確定, 2026-11-06）。record の tail（残りの field を表す型）も例外ではない。`never` は値を持たないものの印で、union の単位元（空の union）なので、tail に足しても型は変わらない。`{}` と `{} | never` は同じ型であり、tail の書き方の違いで record 型が別物になることはない。したがって `{ x: 1 }` の型は、有限に書ける record 型として一つに決まる。
- **record の「残り」は、要求側が rigid なときに共変である**（確定, 2026-11-06）。record を「先頭の field `l: A` と、残りの field の型 `R`」として見るとき、要求される側（部分型の右辺、反変の位置、関数の引数側）の残り `S` は、field が決まった rigid な spine に限られる。未知の tail の展開（union・`never`・型変数）は、供給する側（左辺、共変の位置）にだけ現れ、要求側には現れない。要求側 `S` が rigid な spine のとき、`R ≤ S` ならば `{ l: A, ..R } ≤ { l: A, ..S }` である。これは幅の部分型（上）を、先頭以外の field にも同じ形で使うことにあたり、一般の `S` に対する新しい規則ではない。
  first-field-wins のため、残りの側に同名の field が隠れていることがある。**隠れた field は、型の上でも無かったことになる**（確定, 2026-11-06）。先に書いた field が勝つと、隠れた field は値にも残らない（`{ x: 0, x: "a", y: 1 }` は実行すると `{ x: 0, y: 1 }` になる）ので、型も同じである。`{ x: int, x: str, ..R }` と `{ x: int, ..R }` は同じ型であり、残りが rigid な spine でも、推論された未知の tail（union など）でも変わらない。したがって、この式の型は主型として一つに決まる。
  **隠れる field の式も評価される**（確定, 2026-11-06）。record の構築は、書いた順に各 field の式（と spread の式）を評価してから、同名の field のうち先に書いたものを残す。`{ x: log 1, x: log 2 }` は `log 1`、`log 2` の順に評価され、effect も起こり、結果は `{ x: 1 }` になる。`{ x: 3, ..base }` の `base` も、`x` が隠れても全体が評価される。
- 対して `struct`（4.4）は名前で区別される nominal な型で、部分型付けを持たない。
- 型の表示では、省略可能な field は `?` 付きで出る。例: `{width?: 'a} -> 'a | int`。
- record pattern の default（`{ width = 1 }`）が、省略可能な field を生む（章3b.3）。

## 4.4 `struct`　〔`.0` は確定、他は仮採用〕

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

- 構造 projection（確定, 2026-11-04）: `value.(x, y(4))` は `(value.x, value.y(4))` という tuple、`value.{ first: x }` は `{first: value.x}` という record を作る。同じ `value` から複数の field を取り出す略記。

出典: `main:web/docs/ja/reference/structs.md`

## 4.5 `enum`　〔constructor のカリー化は確定、他は仮採用〕

polymorphic variant の型も存在する（確定, 2026-11-04）。綴りは 2 つあり、同じ意味（確定, 2026-11-04）。`:name payload` の pattern（章3b）に対応する型で、閉じた tag の集合を表す。

```yulang
my f(x: :{ready, some int}) = ...         // { } に tag を並べる形
my g(x: :ready | :some int) = ...         // tag ごとに : を付けて | でつなぐ形
```

payload がなければ unit。

- **variant の「残り」は推論される**（確定, 2026-11-04）。`case` が一部の tag だけを拾い、最後の腕で残りを受けるとき、その腕で束縛した値の型は「拾った tag を除いた残り」になる。表示は effect の行と同じ形で、残りを行変数で書く:

  ```text
  list (:str 'a | 'r) -> (list 'a, list 'r)
  ```

  これを引数 `list (:str str | :num int)` に当てると、`'r` は `:num int` になり、結果の型に「文字は全部処理した、残りは数字だけ」が出る。
- **tag は一意で、payload は tag ごとに合流する**（確定, 2026-11-05）。`if b then :id 1 else :id "a"` の型は `:id (int | str)` で、`:id int | :id str` という別々の alternative は持たない。`case` が `:id x` を拾えば `x: int | str` の全体が取れ、payload の一部だけを処理して残りの payload を `'r` に残すことはできない。したがって網羅性は「tag の集合が閉じているか」で決まり、payload の中までは入らない。全部処理して残りが空になることと、網羅性（章3b.4）は同じ条件である。値の variant には effect の stack weight 相当は要らない（tag は handler に捕まえられない）。
- **行変数 `'r` は利用者が注釈に書かない**（確定, 2026-11-04）。注釈に書けるのは閉じた `:str str | :num int` の形だけで、`:str 'a | 'r` は推論された型として hover などに現れる（`'e?` と同じ扱い）。書けるようにするかは、必要が出てから決める。
- 残りが空のときの網羅性との関係、effect の引き算との関係は上のとおり確定した。形式化は `lean/Yulang/Variants.lean`（`traps.md` T-variant）。

```yulang
enum opt 'a = nil | just 'a

enum event:
    moved { x: int, y: int }     // record payload
    named { name: str }
```

- variant は companion module の member（`event::moved`）。修飾なしで使うには `color::red` と書くか、`use color::*` で入れる。prelude が再公開する `just` / `nil` / `ok` / `err` だけが、はじめから修飾なしで使える（確定, 2026-11-04）。
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
- **SCC の中では、型は単相で連立して解く。多相再帰は、全部注釈した binding だけが使える**（確定, 2026-11-05）。SCC の各 binding は、定義が終わるまで型を一つに固定して使い、終わってから一般化する。例外として、**全引数と戻り値の型がすべて書かれた** binding は、その注釈をスキームとして仮定でき、再帰呼び出しのたびに注釈の型変数を別の型で具体化できる。

  ```yulang
  my depth(x: 'a, n: int): int =
      if n == 0: 1
      else: depth((x, x), n - 1) + 1        // 注釈があるので 'a を変えて呼べる
  ```

  - 「全部書かれた」は、型が全部書かれているかだけで決まる。`_` の穴や注釈のない引数があれば、その binding は単相。effect 行は数えない（T3: 注釈の行は検査するだけで、変数を束縛しない）。
  - 注釈の型変数だけが再帰呼び出しで量化される。その関数が推論する effect 行は、再帰の最中は一つの行を共有する。
  - 同じ SCC の他の binding からの呼び出しにも、全部書かれた binding は注釈のスキームが使われる（暫定。相互再帰での扱い）。
- 値の cycle は拒否される。

```yulang
my make x = x
my a = make b
my b = make a              // エラー: 再帰する component の中で computed value を取得している
```

  これは章2の参照順序の規則（評価される位置に現れた関数は呼ばれたとみなす保守的な判定。確定, 2026-11-05）の特別な場合として拒否される。型の SCC とは別に、評価の依存で判定する。

出典: `main:web/docs/ja/reference/types.md` §Value restriction、`main:spec/2026-06-13-computed-fetch-value-restriction.md`

## 4.8 書けない型と、表示に出る型　〔仮採用〕

- 推論結果には union / intersection（`'a | int`、`'a & {width?: any}`）が出ることがある。
  これらを**注釈として直接書くことはできない**（確定, 2026-11-04）。注釈に書ける型は、nominal な型・tuple・record・関数・型変数・`:{...}`（4.5）だけ。値を複数の型から選ぶときは `enum` を作る。H7 の `:ready | :some int` の `|` は polymorphic variant の型の綴りで、一般の union 型を書く構文ではない。
- 注釈を足すと、表示型を意図した公開形に絞れる。表示の規則は章7。

## 確認してほしい点

なし（G5' は H7 で解決）。
