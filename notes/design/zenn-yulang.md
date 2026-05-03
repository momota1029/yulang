[Yulang](https://github.com/momota1029/yulang)という言語を作っています。[Playground](https://yulang.momota.pw/)がもう動きます。「PerlやPythonの様な軽量で違和感のない文法でゆるくサブタイピングがある言語に、厳格な型推論とAlgebraic Effects and Handlers、省略可能レコードや多相バリアントを入れた強力な言語」がコンセプトです。

## Algebraic Effects and Handlers
エフェクトはその中でも最たるものです。まずは以下を見てください:
```yulang
pub act out:
    our say: str -> ()

our add_and_say() =
    my a = 1 + 2
    out::say a.show
    my b = a + 3
    out::say b.show
    a + b

our listen(x: [_] _, log) = catch x:
    out::say o, k -> listen(k(), log + o + "\n")
    v -> (v, log)

listen add_and_say() ""  // => (9, "3\n6\n")
```

`out::say o, k -> listen(k(), log + o + "\n")`の部分は「`out::say`で計算が一時停止してお伺いを立ててきたので、それに`k ()`でアンサーを与え、次またお伺いが来た時に備えてその結果も`listen`する」という意味です。これ自体が分からなくても「`out::say`した結果が蓄えられているな」というのが見えればOKです。

これを[Playground](https://yulang.momota.pw/)で型推論した結果は
```
add_and_say : unit -> [out] int
listen : Add<std::str::str | α> => α [out; δ] -> β -> [δ] γ | (α, β | std::str::str)
out::say : std::str::str -> [out] unit
```
になります。「エフェクト`β`を取って`γ`を返すという関数型を`α [β] → [γ] δ`」と表します。ここでは引数の型が`[out; δ]`のように足し算されていて、残った`[δ]`がエフェクトとして出ている、という意味です。

ここで書き手は型をほとんど書かなくてよいのです。実際はエフェクトの衛生性のために「この関数はエフェクトを受け取る」という意味で`[_] _`と書く必要があるのですが、そのくらいです。`our say: str -> ()`のような型だけでの定義はMooseなどである程度型注釈に慣れてらっしゃれば読めると思います。

Algebraic Effects and Handlersは非常に強力ですので、後にも触れる必要があります。この言語は純粋関数型言語+部分型推論にAlgebraic Effects and Handlersをくっつけた程度の表現力で、既存の言語のあらゆることを表現しています。

## 空白センシティブな構文
次の特徴は「ML式の関数適用もC式の関数適用もできる」というところです。最後の行に`listen add_and_say() ""`と書いてあると思いますが、これは`listen`に2つの引数を渡している、という意味です。OCamlやMLをやった方、またRubyなどで括弧のない適用に慣れた方なら読めると思います。また括弧付きの関数適用の方が優先順位も高いので、これは人間の目にあった形でパースされます。

この「人間の目にあった形でパースされる」特徴により、様々なことができるようになります。`:`はHaskellの`$`と同じく「後ろの式を飲み込む」構文ですので、
```
out::say: 1 + 2 + 3 + 4
```
と書けばきちんと`out::say(1+2+3+4)`として読み込まれることになります。括弧と言えばとにかく人間の目に負荷のかかる文法であるため、限りなく取り外せるように工夫を凝らしています。

## メソッド指向
オブジェクト指向ではなく、「メソッド指向」です。というのも、レシーバの型によってメソッドを静的に探索して、それが何になるかを決めるという流れになっているためです(そのため、型注釈が必要になる場面もあります)

```
// struct with
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2  // => 25
```

`point`という型に`norm2`というメソッドが紐付けられていることがわかります。こうすることでオブジェクト指向の一番便利な側面である「メソッドを承けるオブジェクトによる様々なオーバーロード」の恩恵を受けられます。オブジェクトのメソッドテーブルを動的に見に行かなくてよいというのも、ある意味では利点です。

後述しますが、型であれば何でもよいので、「エフェクトをとるメソッド」がまさに定義可能であるという点も優れています。

もう少し面白いのは、普通の値だけではなく、参照もreceiverとして扱えるところです。たとえば標準ライブラリでは、リストに対して次のようなメソッドを書けます。

```yulang
our &xs.push x = &xs = $xs.append [x]
```

ここでは`&xs`が更新可能な参照として渡され、`$xs`で今のリストを読み、`&xs = ...`で新しいリストを書き戻しています。つまり、receiverがただの値である場合だけでなく、更新可能な参照である場合にも、同じメソッドの見た目で書けます。

```yulang
point { x: 3, y: 4 }.norm2
xs.len
xs.append ys
&xs.push x
```

`norm2`は`struct point ... with:`で足したメソッド、`len`はrole由来のメソッド、`append`はlistのメソッド、`push`は参照つきreceiverのメソッドです。中身は違いますが、使う側では全部`receiver.method`として読めます。

Yulangでは`x.foo`をすぐに「レコードのフィールド」と決め打ちしません。いったん「`x`に対して`foo`を選ぶ」という形で持っておき、あとで型を見ながら、レコードフィールドなのか、structのメソッドなのか、roleのメソッドなのか、参照用のメソッドなのかを決めます。ここがメソッド指向と呼びたいところです。

## 様々な機能の実装
### 参照
Yulangには、普通の束縛とは別に、参照を扱うための構文があります。これは裏でAE/H(Algebraic Effects and Handlersが長いので以後こう略しますね)が動いています。

```
my $x = 10
&x = 11
$x
```

変数への値の参照は`$x`で行い、その変更は`&x`で行います。これはPerlとRustからそれぞれ着想を得た表現です。実際には以下のライブラリが関わっています。これは`std::var`の中の表記です:

:::details std::varの実装イメージ

```
act ref_update 'a:
    our update: 'a -> 'a

type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
        update_effect: () -> [ref_update 'a; 'e] ()
    our r.update f =
        my loop(x: [_] _) = catch x:
            ref_update::update v, k -> loop:k:f v
        loop:r.update_effect()


act var 't:
    our get: () -> 't
    our set: 't -> ()

    my var_ref() = ref {
        get: \() -> get(),
        update_effect: \() -> set:ref_update::update:get()
    }

    my run(v, x: [_] _) = catch x:
        get(), k -> run v: k v
        set v, k -> run v: k()
```

:::

これを用いることで
```
var::run 10:
    var::set 11
    var::get()
```

に相当するコードに書き換えられ、実行されるというわけです。参照変数は全てこのようにして脱糖されます。

### ジャンクション
ジャンクションという機能はRakuで聞き覚えのある方がいらっしゃるかも知れません。実際にYulangでは次のコードが簡単に動きます:
```
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

構文も全くRakuと同じですが、その再現方法は全く異なります。実は`if`がハンドラー`std::junction::junction::junction`になっていて、effectである`all`と`any`を解釈するようになっています。そのせいで`if`から外に出そうとするとこの式は成立しなくなります(もちろん関数に閉じ込めたり、`junction`を明示的にかけてやれば十分使えます)。

junctionはこのようになっています:

:::details junctionの実装イメージ

```
use std::flow::*
use std::fold::*

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

pub any xs = junction::any xs
pub all xs = junction::all xs
```

:::

### 非決定性計算
これはAE/Hで最もわかりやすい計算でしょう。
```
(each [1, 2, 3] + each [4, 5, 6]).list
```
と書けば、
```
[5, 6, 7, 6, 7, 8, 7, 8, 9]
```
が得られます。これはまさに全通り計算しているだけ、なのですが、`.list`になっているのに気づいたでしょうか。これがまさに「エフェクトに対するメソッド」であって、実際にエフェクトが関わっていないときは`.list`という名前を他に自由にオーバーロードしてよいのです。

undetはこうなっています

:::details undetの実装イメージ

```
use std::flow::*
use std::fold::*

pub act undet:
    pub branch: () -> bool
    pub fail: () -> never
    pub guard b = if b { () } else { fail() }
    pub each xs = sub::sub {
        xs.fold (): \() x -> if branch() { sub::return x } else ()
        fail()
    }
    pub list(x: [_] _) = catch x:
        branch(), k -> std::list::merge list(k true) list(k false)
        fail(), _ -> []
        v -> [v]

    pub logic(x: [_] _) = loop x [] [] with:
        our loop(x: [_] _, queue, res) = catch x:
            branch(), k -> loop(k true, queue + [k], res)
            fail(), _ -> case std::list::uncons queue:
                std::opt::opt::nil -> res
                std::opt::opt::just (k, queue) -> loop(k false, queue, res)
            v -> case std::list::uncons queue:
                std::opt::opt::nil -> res + [v]
                std::opt::opt::just (k, queue) -> loop(k false, queue, res + [v])


    // 何個も解が要らないときにつかう
    pub once(x: [_] _) = loop x [] with:
        our loop(x: [_] _, queue) = catch x:
            branch(), k -> loop(k true, queue + [k])
            fail(), _ -> case std::list::uncons queue:
                std::opt::opt::nil -> std::opt::opt::nil
                std::opt::opt::just (k, queue) -> loop(k false, queue)
            v -> std::opt::opt::just v


    pub (x: [_] _).list = list x
    pub (x: [_] _).logic = logic x
    pub (x: [_] _).once = once x

pub use std::undet::undet::*
```

:::

そして同じ方法でLogicモナド(ちょっとマニアックですが、宣言的プログラミングを模倣する、らしいです)を定義できるので、無限個試して絶対に答えを得る`.once`も使うことができます。ちょっと見てみましょう。

```
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

これは三平方の定理を満たす最初の組を探して、`just (3, 4, 5)`を返すものです。がむしゃらに全通り試しても、`(1,1,1)`、`(1,1,2)`、`(1,1,3)`、...、`(1,1,n)`から抜け出せず1つも値が見つからないように感じますが、これでも上手く行ってしまうのです(これは素直にLogicモナドがすごい)。

## 構文機能
Yulangは構文やちょっとした使い勝手にも実はこだわっていますので、そこからはその詳細について述べます。

まず、Yulangはインデント構文と`{ ... }`の両方を持っています。普段はPythonのようにインデントで書けますし、式の途中に短いブロックを置きたいときは波括弧でも書けます。

```yulang
my f x =
    x + 1

if x > 0:
    x
else:
    0

{ my x = 1; x + 2 }
```

内部的にはINDENT/DEDENTトークンを先に作るのではなく、パーサーが行頭のインデント量を直接見ています。これは実装としては少し変わっていますが、やりたいことは単純で、「人間が見てまとまりだと思うところ」をなるべくそのまま構文木にしたい、ということです。

### 関数適用
先ほども少し触れましたが、Yulangには式の適用が3種類あります。

```yulang
f x y       // ML風
f(x, y)     // C風
f: x + y    // 右側をひとまとまりにして渡す
```

`f x y`は`f`に`x`を渡し、その結果に`y`を渡す、というML風の適用です。`f(x, y)`は見た目がC系の呼び出しに近いので、複数の値をまとめて渡しているように読みやすいところで使えます。Yulangでは複数引数も最終的には関数適用として扱われますが、見た目の負荷を減らすために両方を書けるようにしています。

そして`:`は、後ろの式を大きくひとまとまりにして渡します。

```yulang
out::say: 1 + 2 + 3 + 4

catch x:
    out::say o, k -> k()
    v -> v
```

`out::say: 1 + 2 + 3 + 4`は、だいたい`out::say(1 + 2 + 3 + 4)`という意味です。`catch`や`if`や`for`でも同じ記号を使うので、Yulangの`:`は「ここから右、または下にあるかたまりを渡す」ための記号だと思うと読みやすいです。

### ユーザー定義演算子
演算子はユーザーが定義できます。しかも、中置演算子だけではなく、前置、後置、引数を取らない演算子も定義できます。

```yulang
pub infix (..) 4.0.0 4.0.0 = std::range::inclusive
pub prefix(not) 8.0.0 = std::bool::not
pub nullfix(last) = loop_last()
```

`infix`は`1 + 2`のような中置、`prefix`は`not x`のような前置、`nullfix`は`last`のように単体で現れる演算子です。後置の`suffix`もあります。

優先順位は`4.0.0`のようなベクトルで持っています。普通の整数の優先順位だけでもよいのですが、あとから標準ライブラリやユーザーコードで演算子を足すとき、既存の優先順位の間に入れたくなることがあります。そこで、少し余白のある形にしています。

演算子そのものも、最終的にはroleや普通の関数へ向かいます。たとえば`+`は`Add`、`<`は`Ord`、`xs[i]`は`Index`のような解決に乗ります。ここは「演算子だけ特別な世界にいる」のではなく、メソッド解決や型推論と同じ場所で扱いたい、という設計です。

### 束縛と宣言
値の束縛は`my`、`our`、`pub`から始まります。

```yulang
my local = 1
our package_value = 2
pub exported x = x + 1
```

`my`はローカル、`our`はそのモジュール内の名前、`pub`は外へ公開する名前です。関数定義は左辺に引数を書いていく形です。

```yulang
my add x y = x + y
```

これはだいたい次のlambdaの糖衣として扱われます。

```yulang
my add = \x -> \y -> x + y
```

型や構造体やenumは、今はこのように書きます。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

enum opt 'a = nil | just 'a
```

`with:`はcompanion moduleに近いものを作り、型にメソッドを足すために使っています。`point { x: 3, y: 4 }.norm2`のように呼べるのは、この`with:`の中で`norm2`を定義しているからです。

### レコードと省略可能フィールド
レコードは普通の値として書けます。

```yulang
{ x: 1, y: 2 }
```

少し特徴的なのは、パターン側でdefaultつきフィールドを持てることです。

```yulang
my width_or_default { width = 1 } =
    width
```

これは「引数に`width`があればそれを使い、なければ`1`を使う」という意味になります。省略可能引数のようなものを、関数呼び出し専用の特別構文ではなく、レコードパターンとして表しています。

残りのフィールドを受け取るspreadもあります。

```yulang
my take_width { width = 1, ..rest } =
    (width, rest)
```

こうしておくと、オプションを受け取る関数を書きたいときにも、専用のキーワード引数構文を足さずに済みます。レコードを分解するだけで済むので、言語の小さい機能を組み合わせている感じですね。

### リストとパターン
リストリテラルは標準ライブラリの`list`とつながっています。

```yulang
[]
[1, 2, 3]
[..xs, x]
```

パターンでも同じように書けます。

```yulang
case xs:
    [] -> 0
    [x, ..rest] -> x
```

見た目としてはよくあるリスト構文ですが、内部では`std::list::list 'a`という型へ制約されます。つまり、ただの構文上の配列ではなく、標準ライブラリの型、role、メソッド解決へきちんと乗る値です。

### 多相バリアント
多相バリアントは`:`で表します。

```yulang
:ok
:err "message"
```

型側では`:{ ... }`を使います。

```yulang
:{ ok, err str }
```

通常のenum variantは`opt::just x`のようにpathで表します。一方で多相バリアントは、タグそのものを軽く書きたいので、`:ok`のような構文に分けています。小さい成功失敗や、ちょっとした状態を返したい場面ではこちらの方が読みやすいと思っています。

### do
`do`もあります。ただし、Haskellの`do`記法とはかなり違います。Yulangの`do`は、ざっくりいうと「この後ろの計算をここへ差し込む」ためのmarkerです。

```yulang
my a =
    my x = f(g do)
    x
```

bindingの右辺に`do`がある場合は、後続のブロックを受け取るlambdaを作ります。この例なら、`g`に「この先の計算」を渡すような形に脱糖されます。エフェクトや継続を扱う関数を書いていると、これがあるだけで括弧がかなり減ります。

bindingではない式の中で使うと、後続の式そのものに置き換わるように読めます。

```yulang
my a =
    id(id do)
    1
```

この例なら、`do`の位置に`1`が入る、という見方です。まだ仕様としては揺れている部分もありますが、Yulangでは「ブロックを値として渡す」場面が多いので、そのための軽い構文として入れています。

### ループ制御
`for`は普通のループのように書けます。

```yulang
for x in [1, 2, 3]:
    if x == 2:
        last
    else:
        ()
```

ただし内部では、`std::flow::loop::for_in`とhandlerの仕組みに寄せています。`last`、`next`、`redo`は、ループの外へ飛ぶ特別命令というより、loop controlのeffect operationとして扱う方向です。

ラベルつきloopもあり、`for 'label x in xs:`のような形をパーサーとloweringが扱います。見た目は普通の制御構文ですが、中ではやはりAE/Hと標準ライブラリへつながっています。

ここまでをまとめると、Yulangの構文は「よくある便利構文をたくさん足す」というより、「関数適用、メソッド解決、role、effect handler、標準ライブラリの型へ自然に落ちる書き方を用意する」という方向です。表面は軽く、裏側はできるだけ同じ仕組みに寄せる、というのが目標です。

## その他の機能

ここまでで、エフェクト、参照、ジャンクション、非決定性計算、構文の話をしました。最後に、まだ大きく取り上げていないけれど、Yulangらしさを作っている機能をいくつかまとめておきます。

### roleとimpl
Yulangの`role` / `impl`は、Haskellの型クラスやRustのtraitに近いものです。メソッド解決や演算子解決は、かなりこの仕組みに寄っています。

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y
```

このように書いておくと、次の2つは同じ方向へ解決されます。

```yulang
1.add 2
1 + 2
```

`+`はただの組み込み演算子ではなく、最終的には`Add`の実装へ向かいます。同じように、`==`は`Eq`、`<`は`Ord`、`xs[i]`は`Index`へ向かいます。つまり、演算子もメソッドも「型を見て、使える実装を探す」という同じ流れに乗っています。

関連型もあります。たとえば`Index`は、containerとkeyから返り値の型を決めます。

```yulang
pub role Index 'container 'key:
    type value
    our container.index: 'key -> value
```

標準ライブラリでは、`list 'a`や`str`が`int`や`range`でindexできるように実装されています。ここも、構文としての`xs[i]`を特別扱いしすぎず、roleの仕組みに落とすための設計です。

### 型推論とサブタイピング
Yulangはかなり型を書かずに済むようにしていますが、裏側では型推論がずっと動いています。特にやりたいのは、ML風の型推論に、ゆるいサブタイピングを混ぜることです。

たとえば`int <: float`のような関係を型システム側に持たせると、「整数を浮動小数点数として使える」という実用上よくある広がりを扱えます。ただ、単純にサブタイピングを足すと型推論はすぐ難しくなります。Yulangではsimple-sub系の考え方を土台にして、型注釈を増やしすぎずにこのあたりを扱おうとしています。

エフェクトも型に入ります。`add_and_say : unit -> [out] int`のように、「この関数は`out`というエフェクトを起こしうる」という情報が型に出ます。そしてhandlerを通すと、処理したエフェクトは外へ出なくなります。

この「値の型」「エフェクトの型」「role制約」「サブタイピング」が同じ推論の中にいるのが、Yulangの実験としてかなり大きいところです。

### 標準ライブラリが言語を作る
Yulangでは、構文だけではなく標準ライブラリも言語の見た目をかなり作っています。今の標準ライブラリで、特に見た目に関わっているのはこのあたりです。

- `std::prelude`: 基本role、演算子、よく使うimport
- `std::list`: list型、list literal、`Fold`、`Index`
- `std::range`: `..`や`..<`などのrange
- `std::fold`: `Fold` role
- `std::index`: `Index` role
- `std::flow`: `return`、`last`、`next`、`redo`
- `std::undet`: 非決定性計算
- `std::var`: `$x` / `&x`に関わる参照

たとえば`[1, 2, 3]`はただの配列リテラルではなく`std::list`へつながりますし、`1..`は`std::range`へつながります。`last`や`next`も、ループだけが知っている予約語というより、`std::flow`側の機能として扱う方向です。

これは少し危うい設計でもあります。標準ライブラリとコンパイラの境目が薄くなるからです。ただ、その代わりに、言語本体を小さく保ったまま、強い機能を普通のコードとして増やせます。Yulangでやりたいのはまさにそこです。

### Yumark
Yumarkという文書記法も置いています。これはCommonMarkの拡張のようなものですが、HTML出力に強く寄りすぎた部分や曖昧な部分は削って、Yulangの構文と混ぜやすい形にしようとしています。

たとえばdoc commentはYumarkとしてparseされます。

```yulang
-- 1行のdoc comment

---
# block doc

本文
---
```

Yulang式の中では、`'[]`と`'{}`でYumarkに入れます。

```yulang
'[inline *doc*]
'{
  # Heading
  body
}
```

CommonMark由来のparagraph、heading、list、fenced code、quote、link、image、emphasisなどを持ちつつ、`\ident(...)`や`[doc]:op(args)`のようなYulang寄りの文書作用も持たせる方向です。

これはまだ言語の中心機能というより周辺機能ですが、コードと文書を近いものとして扱いたいので、最初から構文の中に居場所を作っています。

### まだ固まっていないところ
もちろん、まだ実験中の言語なので、細部はかなり揺れています。特にこのあたりは、今後変わる可能性があります。

- `use`やmoduleの公開規則
- effect rowの表記
- type parserとTIR5側のsignature parserの差
- record literalの細かい許容形
- operatorのtoken splittingとheader zone
- `do`の細かい脱糖規則
- どこまでを構文にして、どこからを標準ライブラリへ寄せるか

ただ、少なくとも今の実装では、型推論、サブタイピング、role、record、effect handler、参照、loop controlが同じパイプラインの上で動き始めています。構文だけを増やしているのではなく、それぞれの機能が同じ式の中で噛み合うところまで来ています。

たとえば、`&xs.push x`のような参照つきreceiverのメソッドと、`all xs < any ys`のようなジャンクションが、どちらも型推論とメソッド解決とエフェクトの上で動きます。ここが、今のYulangで一番面白いところだと思っています。

まだ荒いところはたくさんありますが、「軽く書けるのに、裏側では型とエフェクトがきちんと追いかけてくる言語」はかなり手触りがよいです。しばらくはこの方向で、実装を固めながら遊べる範囲を広げていくつもりです。
