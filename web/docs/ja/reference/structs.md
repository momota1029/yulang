# struct と role

nominal な `struct` 型と、`with:` で定義する companion method をまとめる。
`role` と `impl`、type variable に constraint を付ける `where` も扱う。

## Struct

```yulang
struct point { x: int, y: int }
```

`struct` は nominal な record 型である。
値は次のように作る。

```yulang
point { x: 3, y: 4 }
```

## Tuple struct

`tuple struct` は、位置で `field` を持つ nominal な product である。

```yulang
struct user_id(int)
struct point(int, int)

my unwrap value = case value:
    user_id(id) -> id

(unwrap(user_id(7)), point(3, 4))
```

`field` が 1 個でも、`tuple struct` には constructor と対応する constructor `pattern` がある。
括弧を書いても、`user_id(int)` が payload の型へ変わることはない。

## Type parameter

```yulang
struct pair 'a 'b { fst: 'a, snd: 'b }
struct box 'a { value: 'a }
```

struct は type parameter を持てる。
type parameter は `'a` の形で書く。

## Variant の record payload

`enum` `variant` の payload には名前付き `field` を宣言できる。
値の構築とパターンマッチには、同じ `record` の形を使う。

```yulang
enum event:
    moved { x: int, y: int }
    named { name: str }

my coordinates value = case value:
    event::moved { x, y } -> (x, y)
    event::named { name } -> (name.len, 0)

coordinates(event::moved { x: 3, y: 4 })
```

`error` `variant` の名前付き `record` payload も parser は受理する。
ただし、checker は現在、その宣言を `unsupported syntax` として拒否する。
したがって、`record` payload を利用できるのは `enum` `variant` だけであり、`error` `variant` では利用できない。

## 構造 projection

`value.(...)` は `value` から複数の member を選び、`tuple` を作る。
`value.{...}` は選んだ member を改名できる `record` を作る。

```yulang
my source = { x: 3, y: \n -> n + 1 }

source.(x, y(4))                    // (3, 5)
source.{ first: x, next: y(8) }    // {first: 3, next: 9}
```

projection 内の各式は、source を基準に評価する。
`field` を直接選ぶことも、選んだ関数を呼び出すこともできる。

## `with:`

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

`with:` block は struct の companion module へ定義を追加する。
receiver 名を付けた binding は method として登録される。
例の `p` は、method を呼び出した値を表す。
companion の外から見える method にするため、例では `our` を使っている。

同じ `with:` の仕組みは `type` 宣言にもある。
標準ライブラリの `list`、`str`、`ref` も companion module に method を定義している。

## Role

role は、型が実装できる method と optional な associated type の集合である。
role 名の後ろに、その role が parameterize する type variable を置いて宣言する。

```yulang
role Add 'a:
    our a.add: 'a -> 'a

role Eq 'a:
    our a.eq: 'a -> bool
```

method header `our a.method: <type>` の receiver 名 `a` は、実装対象の型の値を表す。

role は associated type を宣言でき、複数の type parameter を持てる。

```yulang
role Index 'container 'key:
    type value
    our container.index: 'key -> value
```

## `impl`

```yulang
impl Add int:
    our x.add y = std::int::add x y

impl Index str int:
    type value = char
    our s.index i = std::text::str::index_raw s i
```

role 名の直後にある型は最初の type parameter を埋め、後続の型が残りを埋める。

struct の `with:` block 内でも `impl` を書ける。

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index i = b.value
```

この場合、enclosing struct が role の最初の type parameter として前に足される。
role 名の後ろに書いた型引数は、残りの parameter を埋める。

## `where`

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

`where` は type variable に role constraint を付ける。
binding body、role body、impl body の中で使える。
role body の `where` は role method へ継承される。
impl body の `where` は、その impl candidate の前提条件になる。
