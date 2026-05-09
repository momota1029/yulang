[Yulang](https://github.com/momota1029/yulang)という言語を作っています。[Playground](https://yulang.momota.pw)がありますので、今回見せるコードは実際に動かせます。

# Algebraic Effects and Handlers
まずはこのコードを見てください:
```perl
undet::once:
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
// => just (3, 4, 5)
```

それぞれ`a`は`1`から順に、`b`は`a`より大きくとり、`c`は`b`より大きくとり、ピタゴラスの3角形になる場合だけを抜き出し(`guard`)、一回だけ(`once`)値を取り出すというコードです。このコードは最小の組`(3,4,5)`を返します。

ちょっと種類は違うのですが、次はこのコードを見てください:
```python
if all [1,2,3] < any [2,3,4]:
    println "すべての左側の数字に対してある右側の数字が存在して、左側の数字を上回る"
```

まさにそのままのコードですが、これが動作するには`all [1,2,3]`という何かに対して`<`を定義する必要があるように見えます。ところが、これは次の様にも定義可能です:
```perl
my lt x y = x < y
if lt(all [1,2,3], any [2,3,4]):
    println "すべての左側の数字に対してある右側の数字が存在して、左側の数字を上回る"
```

これらの不思議なコード類は、全てAlgebraic Effects and Handlers(以下AE/H)によって成立していますし、すべて**標準ライブラリ内で定義されています**。一体どういうものなのでしょうか。

## `return`の例
ここで漸く`return`の話に戻ってきます。Yulangでは明示的に`sub`/`return`を使って
```perl
my first_over limit = sub:
    for x in 0..: if x * x > limit: return x
    return 0

first_over 40  // => 7
```

と書くことが出来ます。結果は`7`です。ここまでは`sub`があるにせよ普通の言語と同じです。では、これはどうでしょうか

```perl
my ret x = return x
my first_over limit = sub:
    for x in 0..: if x * x > limit: ret x
    ret 0

first_over 20  // => 5
```

これも`5`が返ってくる正式な式です。でもこれだけでは`return`の再利用でしかありません。では`return`の本定義を見てみましょう:
```perl
pub act sub 'a:
    pub return: 'a -> never
    pub sub(x: [_] 'a): 'a = catch x:
        return a, _ -> a
        a -> a
```

なんだこれは、と思うかも知れません。`return`は`act`という宣言の中で`never`を返すだけのインターフェースとして定義され、`sub`では計算の中でそれが使われた場合`return a, _ -> a`でその値を返す。本当にこれだけで定義されています。では見てみましょう。
```perl
pub act route 'a:
    pub ret: 'a -> never
    pub route(x: [_] 'a): 'a = catch x:
        ret a, _ -> a
        a -> a

my first_over limit = route::route:
    for x in 0..: if x * x > limit: route::ret x
    route::ret 0

first_over 60  // => 8
```

このようにするだけで`return`は定義できてしまうのです。では他の例を見ていきましょう。

## `undet`の例
今度は簡単な例です。
```python
(each [1,2] + each [3,4]).list  // => [4,5,5,6]
```

これを実現するものはこれです。さっそく`return`が`fold`の中で使われていますね。これは上で**計算**に`return`が現れたら捕捉する、という`sub`の仕組みによるものです
```perl
pub act undet:
    pub branch: () -> bool
    pub reject: () -> never
    pub guard b = if b { () } else { reject() }
    pub each xs = sub::sub {
        xs.fold (): \() x -> if branch() { sub::return x } else ()
        reject()
    }
    pub list(x: [_] _) = catch x:
        branch(), k -> std::list::merge list(k true) list(k false)
        reject(), _ -> []
        v -> [v]
```

見てもらいたいのは`list`の方ですね。`branch(), k`という風に`k`という変数を取っていることに気づいたでしょうか。`k`は`return`でいうなら「もしこのとき`return`しなかったら続いていた計算」を指します。よって、`true`/`false`を代入してそれを配列に入れて別々に計算することで、全通りを計算し尽くすことが出来るのです。

他にも`last`(`break`)/`next`(`continue`)/`redo`などがライブラリ側で動いています。これらも「途中で現在の計算を抜け、handler側で解釈する」という点では`return`と同じ系統なので、ここでは詳しい仕組みは割愛します。

このようにAE/Hというのはあらゆる計算の命令を後から注入してみたり、計算の続きを好きに扱ったり出来る仕組みとして何年も前から話題になっており、[Koka](https://koka-lang.github.io/koka/doc/book.html)や[Effekt](https://effekt-lang.org/)、[Eff](http://www.eff-lang.org/)や[Unison](https://www.unison-lang.org/)など様々な言語が実装され、中にはHaskellの中で動くExtensible Effectsというライブラリがあったり、後付で取り込んだ[OCaml](https://ocaml.org)という言語もあったりします。

# Yulangの特徴
様々な言語があり、それぞれによいところがあります。Yulangはいいなと思ったところを採り入れたり、独自の考えを採用したりしてできるだけ便利に使ってもらえるように考えています。

## エフェクト送出が普通の関数に見える
これは[Koka](https://koka-lang.github.io/koka/doc/book.html)などが採用している戦略です。AE/Hの説明では、operationを`perform`する、という形で紹介されることがありますが、ユーザがそれを明示するのはおまじないのように見えてしまうかも知れません。それをKokaと同じように自動化することで余計な操作や定義を省くことが出来ています。

## 同じメソッド記法で値も計算も扱える
dot selection自体はKokaやRustにもある考え方です。Yulangも、receiverの型に合わせて静的にメソッドを決める方向を採っています。

たとえば普通の構造体には、次のようにメソッドを足せます。
```perl
struct point { x: int, y: int } with:
    pub p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2  // => 25
```

Yulangには`role`という仕組みもあります。これはHaskellの型クラスやRustのtraitに近いものです。たとえば足し算は、概念的には次のようなroleに向かいます。
```perl
role Add 'a:
    pub a.add: 'a -> 'a

impl Add int:
    pub x.add y = std::int::add x y
```

こうしておくと、role由来のメソッドも同じ記法で呼べます。
```perl
1.add 2
1 + 2
```

`1 + 2`のような演算子も、`Add int`の実装を使うものとして扱えます。ここまでは「receiverの型を見てメソッドを探す」という話です。Yulangではそれを、普通の値だけではなく、エフェクトを含む計算にも広げています。

たとえば
```perl
(each [1,2] + each [3,4]).list
```
の`.list`は、単にリストのメソッドというより、「この計算に残っている非決定性をリストとして解釈するhandler」です。同じ計算に`.once`を付ければ最初の成功だけを取り出せます。値のメソッド、role由来のメソッド、計算に対するhandlerを、なるべく同じ読み方にしたいわけです。

## できるだけ括弧を書かずに済む文法を採用している
Yulangは、見た目としてはPerlやPythonのように軽く読めることをかなり重視しています。AE/Hやhandlerは強力ですが、毎回括弧や専用構文が目立つと、普通の制御構造としては読みにくくなってしまいます。

そのため、Yulangには関数適用の書き方がいくつかあります。
```perl
f x y       // ML風
f(x, y)     // C風
f: x + y    // 右側をひとまとまりにして渡す
```

`f x y`はML系の関数適用で、`f(x, y)`はC系の呼び出しに近い見た目です。複数引数も内部的には関数適用に寄せていますが、人間が読むときには括弧つきの方が自然な場面もあるので両方を書けるようにしています。

`:`は、右側や次のインデントブロックをひとまとまりにして渡すための記号です。
```perl
out::say: 1 + 2 + 3 + 4

catch x:
    branch(), k -> list(k true) + list(k false)
    v -> [v]
```

`out::say: 1 + 2 + 3 + 4`は、だいたい`out::say(1 + 2 + 3 + 4)`のように読めます。`catch`や`if`や`for`でも同じ記号を使うので、Yulangの`:`は「ここから右、または下にあるかたまりを渡す」ための記号だと思うと読みやすいです。

また、インデント構文と`{ ... }`の両方を使えます。
```perl
my f x =
    x + 1

if x > 0:
    x
else:
    0

{ my x = 1; x + 2 }
```

普段はPythonのようにインデントで書き、式の途中に短いブロックを置きたいときは波括弧で書けます。`undet::once:`のような書き方も、この「ブロックをそのまま引数として渡す」構文の上に乗っています。

## レコードやバリアントも普通に使える
ここまでAE/Hの話ばかりしてきましたが、もちろん普通の計算を書くための機能も入っています。たとえばレコードはそのまま値として書けます。
```perl
my p = { x: 3, y: 4 }
p.x * p.x + p.y * p.y  // => 25
```

パターン側にはデフォルトつきフィールドも書けます。
```perl
my area { width = 1, height = 1 } = width * height

area { width: 3, height: 4 }  // => 12
area { width: 3 }             // => 3
area {}                       // => 1
```

これは省略可能引数のためだけに専用構文を作るのではなく、レコードパターンとして扱う、という方向です。データを組み立てる機能と、関数の引数を受け取る機能が同じ見た目に寄っています。

enumもあります。
```perl
enum opt 'a = nil | just 'a

my head xs = case xs:
    [] -> opt::nil
    [x, .._] -> opt::just x
```

さらに、多相バリアントも入れています。これは小さい成功失敗や状態を返すときにも便利ですが、引数として受け取るときにもかなり便利です。Rubyのsymbolに値をくっつけられるようになったもの、と考えると雰囲気が近いかも知れません。
```perl
my parse_int s =
    if s == "42":
        :ok 42
    else:
        :err "not an int"

my button option = case option:
    :label text -> "<button>" + text + "</button>"
    :disabled -> "<button disabled></button>"

button: :label "send"
button: :disabled
```

型側では`:{ ok int, err str }`や`:{ label str, disabled }`のような形になります。きちんと名前を付けたいデータには`enum`を使い、関数に渡す小さいオプションや、ちょっとしたタグ付きの値には多相バリアントを使う、という棲み分けです。

## 標準ライブラリが言語を作る
ここまでをまとめると、Yulangは「AE/Hがある言語」というだけではなく、普通の関数、レコード、enum、多相バリアント、role、メソッド、演算子、ブロック構文を同じ方向へ寄せようとしている言語です。

特に大事なのは、言語の見た目のかなりの部分を標準ライブラリ側で作っているところです。`return`、`last`、`next`、`redo`、`each`、`guard`、`.list`、`.once`、`+`、`<`などは、全部がコンパイラだけの特別扱いとして存在しているわけではありません。構文としての入口はありますが、その先では標準ライブラリの定義、role、effect handlerへできるだけ流していきます。

こうしておくと、言語本体を小さく保ったまま、強い機能を普通のコードとして増やせます。`return`をユーザが定義できる、というのはその一例です。Yulangでやりたいのは、特殊な機能を無限に増やすことではなく、普通のコードに見えるものが型推論、role、AE/Hの上で自然に動くようにすることです。

# おわりに
今回は`return`をユーザが定義できる、というところからYulangのAE/Hを紹介しました。

もちろん、実装はまだ動いている途中です。型推論、role、effect handler、標準ライブラリの境目をどこまで自然につなげられるかを試している段階です。ただ、少なくとも`return`、非決定性計算、ジャンクション、ループ制御のようなものを、かなり同じ仕組みの上に置けるところまでは来ています。

こういう方向の言語に興味がある方は、ぜひ[Playground](https://yulang.momota.pw)で触ってみてください。
