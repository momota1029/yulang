# Yulang 言語概要

このページは、現在の Yulang をユーザ目線で説明する overview である。Yulang はまだ実験的な言語なので、ここで書いている内容は安定仕様ではなく、現時点の実装を説明するものとして読むのがよい。

英語版は [overview.md](overview.md) にある。

## Yulang とは

Yulang は、式指向のプログラミング言語である。型推論、構造的な型、role、代数的 effect を中心にしている。

日常的なコードは短く書けるようにしつつ、早期 return、loop、局所参照、非決定的探索、effectful な boolean 条件のような制御も、できるだけ型と effect の中で見えるようにしている。多くの機能は、effect、handler、role、標準ライブラリ定義で表現され、それをいくつかの構文規則がつないでいる。

現在の主な機能は次の通りである。

- indentation block と brace block
- local binding と public binding
- struct、enum、nominal `type`、companion method
- record、tuple、list、enum pattern
- Simple-sub 系の subtyping 付き型推論
- role による ad-hoc 多相
- ユーザー定義演算子
- algebraic effect と `catch` handler
- 早期脱出のための `sub:` / `return`
- `last`、`next`、`redo` を持つ `for` loop
- `$x` と `&x = value` による明示的な参照構文
- `std::undet` による非決定的計算
- `std::junction` による effectful boolean condition

## 小さなプログラム

```yulang
struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

これは nominal type `point` を定義し、`with:` で method を追加し、値を作って `.norm2` を呼ぶ。

compiler は次を登録する。

- `point` という型
- `point` という constructor
- `point::x` と `point::y` という field accessor
- `point::norm2` という companion method

表面構文の `.norm2` は、receiver の型が推論で十分に分かったあとに解決される。

## 実行する

file を実行するには `--run` を使う。

```bash
cargo run -q -p yulang -- --run examples/01_struct_with.yu
```

public binding の推論結果を見るには `--infer` を使う。

```bash
cargo run -q -p yulang -- --infer examples/08_types.yu
```

出力例:

```text
answer : int
twice : Add<α> => α -> α
```

`Add<α>` の部分は role requirement である。`twice` は `Add` の実装を持つ任意の型 `α` で使える、という意味になる。

## ソースファイルと module

Yulang の source file は module として扱われる。import には `use` を使う。

```yulang
use std::undet::*
use std::list::{map, filter}
```

普通の entry file では、compiler が prelude を暗黙に import する。

```yulang
use std::prelude::*
```

標準ライブラリの実体は `lib/std` にあるが、言語内の module path は `std::...` である。

## block と binding

Yulang は式指向である。block は statement を順に評価し、最後の式を値として返す。

```yulang
{
    my x = 1
    my y = 2
    x + y
}
```

binding は local にも exported にもできる。

```yulang
my local_value = 1
our shown_by_infer = 2
pub exported = 3
```

関数の引数は binding header に直接書ける。

```yulang
our twice x = x + x
```

これは関数値として振る舞う。

```yulang
our twice = \x -> x + x
```

## layout

block は indentation でも書ける。

```yulang
if x == 0:
    1
else:
    2
```

brace でも書ける。

```yulang
if x == 0 { 1 } else { 2 }
```

colon form は、application と block を短く書くためにも使われる。

```yulang
sub:
    return 1
```

## データ型

### struct

`struct` は nominal な record-like type を定義する。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
```

値の構築には record syntax を使う。

```yulang
point { x: 3, y: 4 }
```

field は生成された accessor と selection syntax から使える。

```yulang
my p = point { x: 3, y: 4 }
p.x
p.norm2
```

### enum

`enum` は nominal な variant type を定義する。

```yulang
enum opt 'a = nil | just 'a
```

variant は pattern で match できる。

```yulang
case value:
    just x -> x
    nil -> 0
```

標準 prelude は `std::opt::*` を re-export しているので、普通の file では
`opt::` prefix なしで `just` と `nil` を使える。

### nominal `type`

`type` は nominal type を宣言し、companion module を開く。

```yulang
type list 'a with:
    our xs.append ys = std::list::append xs ys
```

現在の実装では、`type` は type alias ではない。opaque type、primitive type、self-structured nominal type、そして companion method のために使われる。

`type` は `struct self` で内部 field shape を定義できる。

```yulang
type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
        update_effect: () -> [ref_update 'a; 'e] ()
```

## pattern

pattern は関数引数、`case`、`catch`、local binding で使われる。

```yulang
my area({width = 1, height = 2}) = width * height
```

これは default value を持つ record pattern である。呼び出し側から見ると、両方の field が optional になる。

```yulang
area { width: 3 }
area {}
area { width: 3, height: 4 }
```

field が無いとき、default expression が評価される。後ろの default は前の field を参照できる。

```yulang
my next_area({width = 2, height = width + 1}) = width * height
```

list pattern には prefix、spread、suffix がある。

```yulang
case xs:
    [] -> 0
    [head, ..tail] -> head
```

## role と演算子

role は Yulang の ad-hoc 多相の仕組みである。

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y
```

演算子は prelude によって role method や関数へ接続された普通の binding である。

```yulang
our twice x = x + x
```

推論結果は次のようになる。

```text
twice : Add<α> => α -> α
```

これは `+` が `int` 固定ではなく、`Add` role によって解決されることを意味する。

ユーザも fixity と binding power を指定して演算子を定義できる。

```yulang
pub infix (++) 4.0.0 4.0.0 = append
```

## effect と handler

Yulang は algebraic effect を持つ。`act` は operation を宣言する。

```yulang
act console:
    pub read: () -> str
    pub write: str -> ()
```

`catch` は effect を起こしうる計算を処理する。

```yulang
catch action:
    some_effect payload, k -> k payload
    value -> value
```

effect arm は operation の payload と continuation を受け取る。continuation を呼ぶと、捕まえた地点以降の計算が再開される。

## `sub:` と `return`

早期 return は effect で実装されている。

```yulang
sub:
    return 1
```

標準ライブラリは `return` operation を持つ `sub` effect を定義している。`sub:` 構文は標準 handler を適用するので、直接的な書き方で早期脱出を書ける。

loop と組み合わせることもできる。

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

## `for`、`last`、`next`、`redo`

`for` には専用構文があるが、反復そのものは標準の `Fold` role に基づいている。

```yulang
for x in 0..:
    if x == 5: last
    else: ()
```

lowerer は loop を次のような呼び出しへ変換する。

```text
std::flow::loop::for_in xs (\x -> body)
```

`last`、`next`、`redo` は loop effect の operation であり、prelude operator として表面に出ている。

## 参照

参照は明示的に書く。

```yulang
{
    my $x = 10
    &x = $x + 1
    $x
}
```

`$x` は現在値を読む。`&x = value` は新しい値を書く。

内部的には、これは通常の mutable slot ではなく、`std::var::var` をもとにした局所 synthetic effect として実装される。そのため、参照の挙動も effect system に参加する。

## 非決定的計算

`std::undet` module は非決定的計算を定義する。

```yulang
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).list
```

`each` は collection から値を 1 つ選ぶ。`.list` は計算を実行し、すべての結果を集める。

```yulang
use std::undet::*

{
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}.once
```

`.once` は最初の結果を `opt` 値として返す。

## effectful condition

Yulang の `if` は、`std::junction` を通して effectful な boolean condition を扱える。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

`if` の condition が pure なら、普通の `bool` として扱われる。condition が effectful なら、lowerer が `junction::junction` を挿入し、標準ライブラリがその condition を解釈する。

これは、構文と標準ライブラリが意図的に接続されている場所の 1 つである。

## 型推論

すべての式は、値の型と effect の型を持つ。多くの program では型注釈を書かなくてもよいが、binding を制約したり説明したりするために annotation を書ける。

```yulang
our p.norm2: int = p.x * p.x + p.y * p.y
```

推論器は次を扱う。

- structural record と tuple
- nominal type
- function type
- row-like effect type
- role requirement
- subtyping

public な推論結果を見るには `--infer` を使う。

## まだ実験的なところ

現在の実装には、parser には存在するが言語機能としてはまだ固まっていないものがある。特に rule syntax と mark syntax は parse できるが、通常の Yulang 式としての意味はまだ実装されていない。

runtime lowering と monomorphization にも制限がある。推論は成功するが、dirty な開発 workspace では residual polymorphic runtime IR が残って実行できない example もある。

この overview は「今の言語がどう動くか」の説明であり、「今後も変わらない安定仕様」ではない。

## 次に読む場所

- `examples/*.yu` は小さな実行可能 program を置いている。
- `lib/std/*.yu` は、言語の多くの振る舞いが標準ライブラリでどう書かれているかを示している。
- `notes/design/yulang-language-report.md` は、実装から抽出したより深い調査レポートである。
