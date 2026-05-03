[Yulang](https://github.com/momota1029/yulang)といいます。まだ実験中の言語だけれど、[Playground](https://yulang.momota.pw)があるので、まずはそこで触ってみるのが一番早いと思う。

今のYulangは「型推論がある、でもMLそのものではない」言語を目指している。とくに、型推論、subtyping、代数的エフェクト、レコード、軽い構文を同じ場所でうまく動かすことを試している。

```yu
// struct with
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

この例では `point` という構造体を作り、`with:` の中で `norm2` というメソッドを足している。型注釈を書かなくても、Playground の右側に推論された型が出る。

Yulangでは、列多相だけに頼るのではなく、simple-sub をもとにした subtyping を型推論に組み込んでいる。たとえば `int <: float` のような関係を型システム側に持たせることで、実用的な暗黙の広がりを扱えるようにしている。

もう一つ大きいのはエフェクトだ。Yulangでは、エフェクトを単に「この式は io を持つ」と足していくのではなく、handler がエフェクトを引くことも型に表したい。たとえば概念的には、

```text
α [io; β] -> [β] γ
```

のように、「io を含む計算を受け取り、io を処理して、残りの β だけを外へ出す」という見方をする。引き算というより、逆足し算に近い。

非決定性計算もこの仕組みの上に乗っている。

```yu
(each [1, 2, 3] + each [4, 5, 6]).list
```

これは全ての組み合わせを列挙して、

```text
[5, 6, 7, 6, 7, 8, 7, 8, 9]
```

のような値になる。

`guard` と無限範囲を組み合わせると、探索っぽいことも書ける。

```yu
({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}).once
```

これは三平方の定理を満たす最初の組を探して、`just (3, 4, 5)` を返す。

構文面では、Python の `:` と Haskell の `$` / `do` を合わせたような `:` を持っている。括弧を減らしつつ、ブロックや関数適用を書けるようにしたい。

```yu
for x in 0..:
    if x == 5: last
    else: ()
```

`for` と `last` / `next` / `redo` は、ループ制御をエフェクトとして扱う方向で実装している。普通の構文に見えるけれど、中では handler と effect の仕組みにつながっている。

レコードも少し変わっていて、省略可能レコードを入れている。これにより、省略可能引数のような書き味を、関数呼び出し専用の特別構文ではなく、レコードの仕組みとして扱える。

## 参照、メソッド、junction

Yulangには、普通の束縛とは別に、参照を扱うための構文がある。

```yulang
my $x = 10
&x = 11
$x
```

`my $x = 10` は、値 `10` を持つ参照を作る。
`$x` はその参照から値を読む構文で、`&x = 11` は参照へ値を書き込む構文になっている。

これは「変数を再代入できる」というより、読み書きできる場所を明示的に扱うためのものだ。
読むときには `$` が付き、書くときには `&` が付くので、式の中でどこが参照の読み書きなのかが見える。

```yulang
my $x = 10
my $y = 20

&x = 11
&y = 21

($x, $y)
```

この式は `(11, 21)` になる。

ここまでは普通の参照っぽいけれど、Yulangで面白いのは、この参照がメソッド解決にも乗るところだ。
たとえば標準ライブラリでは、リストに対して次のようなメソッドを書ける。

```yulang
our &xs.push x = &xs = $xs.append [x]
```

ここでは `&xs` が更新可能な参照として渡され、`$xs` で現在のリストを読み、`&xs = ...` で新しいリストを書き戻している。
つまり、receiver がただの値である場合だけでなく、更新可能な参照である場合にも、同じメソッドの見た目で書ける。

このあたりはかなり気に入っている。
Yulangでは `x.foo` をすぐに「レコードのフィールド」と決め打ちしない。
いったん「`x` に対して `foo` を選ぶ」という形で持っておき、あとで型を見ながら、レコードフィールドなのか、struct のメソッドなのか、role のメソッドなのか、参照用のメソッドなのかを決める。

だから、次のようなものが同じ文法の上に乗っている。

```yulang
point { x: 3, y: 4 }.norm2
xs.len
xs.append ys
&xs.push x
```

`norm2` は `struct point ... with:` で足したメソッド、`len` は `Len` role、`append` は `list` のメソッド、`push` は参照つき receiver のメソッド、というように中身は違う。
でも、使う側では全部 `receiver.method` として読める。

もう一つ、最近かなり面白いと思っているのが `junction` だ。
Yulangには非決定性計算のための `undet` があるけれど、それとは別に、boolean の合成を effect として扱う `junction` も標準ライブラリに入れている。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    2
```

これはかなり変な式に見える。
`all [1, 2, 3] < any [2, 3, 4]` は、左側の全要素が右側のどれかより小さい、というような読み方になる。
今の実装では、この式が普通に型推論と演算子解決を通って動く。

標準ライブラリ側では、`any` と `all` はだいたいこういう形で書かれている。

```yulang
pub act junction:
    my or: () -> bool
    my and: () -> bool
    my ret: bool -> never

    pub any xs = sub::sub:
        xs.fold (): \() x -> case or():
            true -> sub::return x
            false -> ()
        ret false

    pub all xs = sub::sub:
        xs.fold (): \() x -> case and():
            true -> sub::return x
            false -> ()
        ret true

    pub junction(x: [_] _) = catch x:
        or(), k -> junction(k true) or junction(k false)
        and(), k -> junction(k true) and junction(k false)
        ret b, _ -> b
```

`any` や `all` 自体は特殊構文ではない。
`act` で effect を作り、`fold` と `catch` で意味を与えている。
そして比較のところでは、`<` が普通に `Ord` role のメソッドとして解決される。

つまりこの例では、

- `all` / `any` は effect handler で動く
- `<` は role / impl による method 解決で動く
- list の `fold` も role method として動く
- それらが普通の `if` の条件式として合成される

ということが起きている。

これは、Yulangでやりたいことがかなり小さい形で出ている例だと思う。
構文だけを増やしているのではなく、参照、メソッド、role、effect handler、標準ライブラリの関数が、同じ式の中で噛み合っている。

内部的にはまだ粗いところも多いけれど、`&xs.push x` のような参照メソッドと、`all xs < any ys` のような junction が同じ仕組みの上で動くようになってきた。
この方向にはかなり手応えがある。


## もう少し仕様寄りにまとめると

ここまで雰囲気を中心に書いたけれど、Yulang の今の仕様をもう少し整理すると、だいたい次のようになる。
まだ動きながら変わっている言語なので、これは「最終仕様」というより、今のコンパイラと標準ライブラリから見える現状のメモだ。

### 構文

Yulang はインデント構文と `{ ... }` の両方を持っている。
Python のようにインデントでブロックを書けるけれど、内部的には INDENT / DEDENT トークンを作らず、パーサーが行頭のインデント量を直接見ている。

```yulang
my f x =
    x + 1

if x > 0:
    x
else:
    0
```

式の適用は 3 種類ある。

```yulang
f x y       // ML 風
f(x, y)     // C 風
f: x + y    // 右側をひとまとまりにして渡す
```

`:` は Yulang ではかなり重要で、ブロック導入にも、関数適用にも使う。
たとえば handler や loop では、括弧を増やさずに計算のかたまりを渡せる。

```yulang
catch x:
    op(), k -> k()
    v -> v
```

演算子はユーザー定義できる。
fixity は `prefix` / `infix` / `suffix` / `nullfix` の 4 種類で、優先順位は `4.0.0` のようなベクトルとして持っている。

```yulang
pub infix (..) 4.0.0 4.0.0 = std::range::inclusive
pub prefix(not) 8.0.0 = std::bool::not
pub nullfix(last) = loop_last()
```

### 束縛と宣言

値の束縛は `my` / `our` / `pub` から始まる。

```yulang
my local = 1
our package_value = 2
pub exported x = x + 1
```

関数定義は、左辺に引数を書いていく形になる。

```yulang
my add x y = x + y
```

これはだいたい次のような lambda の糖衣として扱われる。

```yulang
my add = \x -> \y -> x + y
```

型や構造体や enum は、今はこういう形で書く。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

enum opt 'a = nil | just 'a
```

`with:` は companion module に近いものを作り、型にメソッドを足すために使っている。

### role と impl

Yulang の `role` / `impl` は、型クラスや trait に近い。
receiver method の解決や、演算子の解決にも使っている。

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y
```

この状態で、次のように書ける。

```yulang
1.add 2
1 + 2
```

`+` は最終的には `Add` の実装に向かう。
同じ仕組みで、`==` は `Eq`、`<` は `Ord`、`xs[i]` は `Index` に向かう。

関連型も使っている。
たとえば `Index` は、container と key から返り値の型を決める。

```yulang
pub role Index 'container 'key:
    type value
    our container.index: 'key -> value
```

標準ライブラリでは、`list 'a` と `str` が `int` や `range` で index できるように実装されている。

### レコードと省略可能フィールド

レコードは普通の値として使える。

```yulang
{ x: 1, y: 2 }
```

パターン側では、default つきフィールドを持てる。

```yulang
my width_or_default { width = 1 } =
    width
```

これは「引数に `width` がなければ `1` を使う」というような、省略可能引数に近い書き味になる。
ただし関数呼び出し専用の特別構文ではなく、レコードパターンの仕組みとして扱っている。

spread もある。

```yulang
my take_width { width = 1, ..rest } =
    (width, rest)
```

### リストとパターン

リストリテラルは標準ライブラリの `list` とつながっている。

```yulang
[]
[1, 2, 3]
[..xs, x]
```

パターンでも同じように書ける。

```yulang
case xs:
    [] -> 0
    [x, ..rest] -> x
```

このあたりは、構文としては軽く見えるけれど、内部では `std::list::list 'a` という型へ制約される。

### poly variant

poly variant は `:` で表すことにしている。

```yulang
:ok
:err "message"
```

型側では `:{ ... }` を使う。

```yulang
:{ ok, err str }
```

通常の enum variant は `opt::just x` のように path で表す。
一方で poly variant は、タグそのものを `:` で軽く書くためのものとして分けている。

### エフェクト

Yulang のエフェクトは `act` で宣言する。

```yulang
act undet:
    our branch: () -> bool
    our fail: () -> never
```

operation は普通の関数のように呼べる。
ただし、その呼び出しは effect row に `undet` のような印を残す。
それを `catch` が処理する。

```yulang
my det(x: [_] _) = catch x:
    undet::branch(), k -> det(k true)
    undet::fail(), _ -> []
    v -> [v]
```

handler は operation を処理し、残った effect だけを外へ出す。
この「処理した effect を引く」感じを型で表したい、というのが Yulang の大きな実験の一つだ。

### ループ制御もエフェクト

`for` は構文としては普通の loop に見える。

```yulang
for x in [1, 2, 3]:
    if x == 2:
        last
    else:
        ()
```

ただし内部では、`std::flow::loop::for_in` と handler の仕組みに寄せている。
`last` / `next` / `redo` は、ループの外へ飛ぶ特殊命令というより、loop control の effect operation として扱う方向になっている。

ラベルつき loop もあり、`for 'label x in xs:` のような形をパーサーと lowering が扱う。

### do

`do` は Haskell の `do` 記法ではなく、ブロックの「ここから後ろ」を差し込むための marker として使っている。

```yulang
my a =
    my x = f(g do)
    x
```

binding の右辺に `do` がある場合は、後続のブロックを受け取る lambda を作る。
この例なら、ざっくり言うと `g` に `\x -> x` のような後続計算を渡す形になる。

```yulang
my a =
    id(id do)
    1
```

binding ではない式の中の `do` は、後続の式そのものに置き換わる。
この例なら `do` の位置に `1` が入る、という見方で読める。

### 参照

参照は `$x` と `&x` で明示する。

```yulang
my $x = 10
&x = 11
$x
```

`$x` は読む側、`&x` は更新する側の名前として扱われる。
標準ライブラリ側では `var` / `ref` / `ref_update` という effect に寄せた形で表現している。

このため、Yulang の参照は「普通の変数を再代入できるようにする」というより、読み書きできる場所を effect の世界に乗せるための構文になっている。

### 標準ライブラリ

今の標準ライブラリで、言語の見た目に強く関わっているのはこのあたり。

- `std::prelude`: 基本 role、演算子、よく使う import
- `std::list`: list 型、list literal、`Fold`、`Index`
- `std::range`: `..` や `..<` などの range
- `std::fold`: `Fold` role
- `std::index`: `Index` role
- `std::flow`: `return`、`last`、`next`、`redo`
- `std::undet`: 非決定性計算
- `std::var`: `$x` / `&x` に関わる参照

つまり Yulang は、構文だけで完結しているというより、構文、型推論、role、effect、標準ライブラリがかなり密につながっている。

### Yumark

Yumark は CommonMark の拡張として置いている文書記法だ。
Markdown っぽく書けるけれど、曖昧なところや HTML 出力専用のところは削り、Yulang の構文と混ぜやすい形にしている。

たとえば doc comment は Yumark として parse される。

```yulang
-- 1 行の doc comment

---
# block doc

本文
---
```

Yulang 式の中では、`'[]` と `'{}` で Yumark に入れる。

```yulang
'[inline *doc*]
'{
  # Heading
  body
}
```

CommonMark 由来の paragraph、heading、list、fenced code、quote、link、image、emphasis などを持ちつつ、`\ident(...)` や `[doc]:op(args)` のような Yulang 寄りの文書作用も持たせる方向だ。

### まだ固まっていないところ

もちろん、まだ仕様として細部が揺れているところもある。

- `use` や module の公開規則
- effect row の表記
- type parser と TIR5 側の signature parser の差
- record literal の細かい許容形
- operator の token splitting と header zone

ただ、少なくとも今の実装では、型推論、subtyping、role、record、effect handler、参照、loop control が同じパイプラインの上で動き始めている。
ここが Yulang の一番面白いところだと思っている。
