# 構造体とロール

nominal な record 型を作る `struct`、companion module へ method を足す `with:`、type 越しに振る舞いをまとめる `role` と `impl`、そして type variable に制約を付ける `where` を扱う。

## Struct

```yulang
struct point { x: int, y: int }
```

`struct` は nominal な record type である。値は次のように作る。

```yulang
point { x: 3, y: 4 }
```

## Type parameter

```yulang
struct pair 'a 'b { fst: 'a, snd: 'b }
struct box 'a { value: 'a }
```

type parameter は `'a` の形で書く。

## `with:`

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

`with:` block は struct の companion module へ定義を追加する。receiver 名を付けた binding は method として登録される。例では、companion の外から見える method にするために `our p.norm2` と書いている。

同じ `with:` の仕組みは `type` 宣言にもある。標準ライブラリの `list`、`str`、`ref` も companion module に method を定義している。

## Role

role は interface である。型が提供すべき method と associated type を宣言する。

```yulang
role Add 'a:
    our a.add: 'a -> 'a

role Eq 'a:
    our a.eq: 'a -> bool
```

receiver 名 `a` は、実装対象の型の値を表す。

associated type を持つ role:

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
    type value = str
    our s.index i = std::str::index_raw s i
```

role 名の後ろの型引数が role の type parameter を埋める。

struct の `with:` block 内でも `impl` を書ける。

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index i = b.value
```

この場合、enclosing struct が role の最初の type parameter として前に足され、role 名の後ろに書いた型引数は残りの parameter を埋める。

## `where`

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

`where` は type variable に role constraint を付ける。binding body、role body、impl body の中で使える。role body の `where` は role method へ継承され、impl body の `where` はその impl candidate の前提条件になる。
