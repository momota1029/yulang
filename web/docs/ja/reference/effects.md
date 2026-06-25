# エフェクト

Yulang の副作用は algebraic effect として扱う。effect は宣言され、
operation request として呼び出され、handler で処理され、型に追跡される。

## 最小例

```yulang
act flip:
    our coin: () -> bool
```

`act` は effect family を作る。operation は `our` または `pub` の
signature として並べる。同名の companion module が作られ、`flip::coin`
や `console::read` のように参照できる。

## 呼び出し

```yulang
my bit = flip::coin()
```

effect operation は普通の関数のように呼べる。operation を呼び出した
computation の型には、その effect が残る。たとえば `flip::coin` を呼ぶ
関数には、effect row に `flip` が入る。

## Handler

```yulang
our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

all_paths:
    my a = if flip::coin(): 1 else: 0
    my b = if flip::coin(): 10 else: 0
    my c = if flip::coin(): 100 else: 0
    a + b + c
```

`catch expr:` は handler である。operation arm は operation の引数と
continuation `k` を受け取る。`k value` を呼ぶと、operation の発生地点へ
値を返し、元の計算を続ける。handler には、内側の計算が普通に値を返した
ときに走る value arm `v -> ...` も書ける。

ここで `flip::coin()` は普通の関数呼び出しに見えるが、実際には operation
request を発生させる。handler は限定継続 `k` を受け取り、`true` と
`false` の両方で再開するので、この例は 3 回の `coin` による 8 通りの
分岐を列挙する。

重要なのは `action: [flip] _` という注釈である。これは **effect capture
contract** であり、この handler boundary が `flip` を処理してよいことを
表す。返り値型と残りの effect はまだ推論される。推論される型の形は次である。

```text
all_paths : 'a [flip; 'b] -> ['b] list 'a
```

つまり、`all_paths` は `flip` と residual row `'b` を持ちうる computation
を受け取り、`flip` だけを処理し、外側には `'b` だけを残す。

ただし「見えている」が重要である。高階関数では、呼び出し元が関数、thunk、data field 内の effectful function 経由で持ち込んだ effect を、内側 handler が勝手に捕まえてはいけない。Yulang はこの境界を内部的には directed stack weight として追跡する。公開型には普通の effect row だけを表示するが、solver は handler 境界から見えている effect だけを引く。

### handler を重ねる

`all_paths` は residual row をそのまま残すので、別の effect を処理する handler と重ねられる。

```yulang
act amount:
    our coin: () -> int

our total_amount(action: [amount] _) =
    my loop(n, action: [amount] _) = catch action:
        amount::coin(), k -> loop(n, k n)
        v -> v
    [loop(1, action), loop(2, action)]

total_amount: all_paths:
    my a = if flip::coin(): amount::coin() else: 0
    my b = if flip::coin(): amount::coin() * 10 else: 0
    my c = if flip::coin(): amount::coin() * 100 else: 0
    a + b + c
```

`all_paths` は `flip` だけを処理し、`amount` は残す。`total_amount` は
`amount` だけを処理する。その結果、`amount` の解釈ごとに list が得られる。

```text
[[111, 11, 101, 1, 110, 10, 100, 0],
 [222, 22, 202, 2, 220, 20, 200, 0]]
```

effect row の読み方はここにある。handler は contract された、つまりその境界から見える
effect だけを取り除き、残りの row は外側へ残す。

### effect family の copy

`act copy = source` は、別の `act` から新しい effect family を宣言する。

```yulang
act original:
    our tick: () -> never

act local = original with:
    our label = "local"
```

copy された operation は copy 先 family の operation として作られる。
`local::tick` は `local` の operation であり、`original::tick` の alias では
ない。

copy は visibility を守る。copy 元 body の `pub` / `our` operation signature
と companion member は継承されるが、copy 元の `my` 宣言は継承されない。copy
先の `with:` body は自分自身の `my` helper を使えるが、copy 元 act の private
helper は見えない。

そのため、copy 元の `our` member が source-private な `my` helper に依存して
いる場合、その member は copy 先で unresolved になりうる。これは意図した
規則であり、`act copy` は copy 元の private 実装詳細を漏らさない。

### handler は shallow

Yulang の handler は **shallow** である。arm は一度だけ operation を受け取り、
`k` で再開された計算は同じ handler に自動では包まれない。再開後に同じ
effect を起こしても、handler は二度目に発火せず、effect はそのまま外側へ
伝播する。

operation を連続で受けたいときは、arm 側で continuation を再度 handler で
包む書き方をする。

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console (k "42")    -- ← run_console で巻き直す
    console::println _, k -> run_console (k ())
    v -> v
```

このリファレンスの handler 例の多くがこの自己再帰形なのはそのため。
operation が 1 度しか起きない前提なら再帰を省ける。effect を繰り返し起こす
任意の計算を扱うときは再帰が必須。

### handler hygiene

handler hygiene は、内側 handler が自分から見える effect は処理してよいが、
外側の呼び出し元が持ち込んだ effect を奪ってはいけない、という規則である。

この性質は、user-defined な early return operator を見ると分かりやすい。

```yulang
pub act sub 'a:
    pub return: 'a -> never
    pub sub(x: [_] 'a): 'a = catch x:
        return a, _ -> a
        a -> a

our g h = sub::sub:
    h 0
    sub::return 1

sub::sub:
    g \i -> sub::return i
    sub::return 2
```

この結果は `0` になる。callback 内の `sub::return i` は外側の `sub::sub` に属する
effect であり、`g` の内側に隠れた handler のものではない。
hygiene がなければ、内側 handler がこれを偶然捕まえ、`g` からの局所 return に変えてしまう。
高階関数では、通常それは望む挙動ではない。

```yulang
my compose f g x = f(g x)
```

`g x` が effect を起こすとしても、`f` の内側に隠れた同じ family の handler がそれを捕まえてはいけない。その effect は `g` 経由で渡された computation のものであり、`f` の内側で発生したものではない。

このため effect annotation は、row を説明するだけでなく、高階境界を越えて
どの effect family を handler に見せるかを決める局所 contract でもある。

`f` に `g(x)` の residual effect を意図的に処理させたいときは、その
contract を明示する。

```yulang
our compose(f, g: _ -> [_] _, x: [_] _) = f g(x)
```

`x: [_] _` は、第三引数が computation であることを表す。`g: _ -> [_] _`
は、`g(x)` の表層 effect が `f` へ流れてよいことを表す。`g` 側の contract
がない場合、Yulang は callback 由来の effect を偶然の捕捉から守る。
compiler-oriented な型表示では、その証拠が `#0[Empty]` のように出ることがある。

## Effect row

```yulang
[console; 'e] str
() -> [console; 'e] str
```

`[...]` の中に effect を並べる。`; 'e` は残りの effect を表す row variable である。`[_]` は annotation 内で推論に任せるための placeholder として使えるが、effect row type そのものの標準形ではない。handler 境界を消す指定でもない。

effect は型引数を持つこともできる。

```yulang
act ref_update 'a:
    our update: 'a -> never
```

そのため row には `ref_update int` のような entry も入る。型表示では Greek variable が出ることがあるが、source annotation では row tail に `e` のような名前を使うのが普通。

effect-row method は nominal value companion ではなく、receiver の effect row から選ばれる。

```yulang
use std::control::nondet::*

(each [1, 2, 3]).list
```

同じ row 内の複数の effect が同名 method を持つ場合、row が絞られるまで selection は ambiguous になる。

## effect 注釈と可視性

effect row annotation には二つの役割がある。

- 関数型に現れる公開 row を説明する。
- 高階境界では、内側 handler が何を見てよいかを決める。

引数位置の `[console] 'a` は effect capture contract であり、受け取る側の
handler がその computation から `console` を処理してよいことを表す。
wildcard annotation の `[_] 'a` は surface contract である。普通の表層 row
は見えるが、他の場所の hygiene evidence を捨てる指定ではない。

callback 引数にそのような contract がない場合、callback 由来の effect は
hygienic に保たれる。その effect を別の callee へ渡すと、推論された scheme
に空の可視性 budget が残り、compiler-oriented な表示では `#id[Empty]` の
ように出ることがある。これは「この occurrence からはその boundary で何も
subtract できない」という証拠であり、新しい effect family ではない。

結果位置の具体 effect annotation は static filter である。外へ出てよい effect を検査するが、runtime marker にはならず、追加の公開 effect としても表示されない。

local reference など標準ライブラリの一部は、data value の中に effectful function を保持する。その内部の handler evidence は private に扱われる。たとえば `ref.update` の内部では `ref_update` が関わるが、公開型には内部 stack id や `AllExcept(...)` evidence ではなく、普通の residual row が出るべきである。

## Propagation

effectful な関数を呼ぶと、その effect は外側へ伝播する。handler がその effect を見て処理できる場所でだけ取り除かれる。

```yulang
our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
```

## `error` 宣言

`error` は、`enum`、throwing operation を持つ `act`、`impl Throw`、`wrap` / `up` companion helper をまとめて生成する短縮構文である。

```yulang
error path_err:
    not_found path
    denied path
    invalid_path path
```

各 variant は data constructor と effect operation の両方として使われる。値として必要な文脈では `path_err` の値になり、effect として必要な文脈では `path_err` effect を発火する operation になる。

`fail`、名指し catch、`wrap`、`from` 集約、`up` の使い方を含む全体像は [エラー](./errors) を参照。

通常の `enum` variant でも `from` は使える。[キャスト](./casts) を参照。

## 関連

- [値と型](./types) — function type と effect row の表示。
- [型推論の理論](./type-theory) — stack 重み付き row と handler hygiene。
