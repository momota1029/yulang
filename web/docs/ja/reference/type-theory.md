# 型推論の理論

このページは、Yulang の型推論が effect と handler をどう扱うかを、公開
reference 向けにまとめる。完全な solver 仕様ではなく、CLI、playground、language server が出す
型を読むための地図である。

現行実装では、handler hygiene を subtype solver の中の **directed stack weight** として表す。
handler は、その weight を通して見えている effect family だけを row から引ける。

## 式は値型と effect row を持つ

Yulang の式は、値の型と effect row を持つ。

```text
e : A ! rho
```

これは「式 `e` は値 `A` を返し、その途中で effect row `rho` の effect を起こす可能性がある」
という意味である。

表面の型表示では、この 2 つをまとめて次のように書く。

```text
[console] str
```

これは、`console` effect を起こす可能性があり、最後に `str` を返す computation value である。

関数型では、返り値側に effect row が付く。

```text
() -> [console] str
```

これは「unit を受け取り、呼ぶと `console` effect を起こしうる `str` を返す関数」である。

## 普通の subtyping

Yulang の推論器は、型をただ等号で揃えるだけではなく、subtyping 制約として扱う。

```text
actual <: expected
```

effect row も同じ graph の中を流れる。

```text
[console] str <: [console; e] str
```

具体的な `console` effect は open row に入る。handler が effect を消した後に残る residual も、
普通の row として同じ graph の中を流れる。

## 単純な row subtraction だけでは足りない理由

直接的なコードだけを見ると、`catch` は内側の row から effect を引いているだけに見える。

```yulang
act console:
    our read: () -> str

our run_console(action: [console; e] 'a): [e] 'a = catch action:
    console::read(), k -> run_console(k "42")
    v -> v
```

ざっくり言えば、`action` の row が `[console; e]` なら、`catch` の外側には `[e]` だけが残る。

ただし高階関数では、「その effect がどこから来たか」が重要になる。

```yulang
my compose f g x = f(g x)
```

`g x` が `last` effect を起こすとしても、`f` の内部にある `last` handler がそれを勝手に捕まえては
いけない。`g` の effect は `compose` の呼び出し元が持ち込んだものであり、`f` の所有物ではない。
この性質を Yulang では **handler hygiene** と呼ぶ。

## directed stack weight

推論器の内部では、型に stack wrapper を付けることがある。

```text
stack(T, S)
```

これは source language に `stack` という型コンストラクタがあるという意味ではない。どの handler
境界が、どの effect family を引いてよいかを覚えるための内部表現である。

subtype 制約は、左右に向きを持つ重みを持つ。

```text
T @L <: @R U
```

- 左重み `L` は active な `take(H)` を持てる。
- 右重み `R` は pure pop だけを持つ。
- `take(H); pop` は cancel するが、`pop; take(H)` は cancel しない。
- 関数引数は反変なので、そこへ入ると左右の向きが入れ替わる。

この向きが重要である。row head を handler が消費できるかを決める前に、左右の重みを一つに潰してはならない。

## `catch` はどう effect を引くか

`catch` が effect 集合 `H` を処理するとき、推論器は row 制約を次の形で見ることがある。

```text
alpha @L <: @R [H; beta]
```

この row head から実際に消費できる集合は次である。

```text
J = H ∩ Common(L)
```

`Common(L)` は、左重みに残る active な `take(...)` family の交差である。
右側の pop は handler に effect を見せない。filter や legacy 互換 marker も active push ではない。

`J` が空なら、この handler はその row から何も消費できない。
handler があるというだけで residual を作ったり、未知 row を勝手に開いたりしない。

`J` が空でなければ、solver は row を分ける。

```text
alpha <: [J; gamma]
gamma @(L - J) <: NWeight(R, beta)
```

`NWeight(R, beta)` は、右側 pop の evidence を residual tail に残す内部 wrapper である。
row head を見せるためには使わない。

同じ subtraction slot には同じ residual 変数 `gamma` を再利用する。これにより、recursive handler が
fresh な tail を無限に作り続けることを避ける。

型引数を持つ effect family は family path で突き合わせるが、引数は捨てない。`ref_update int` と
`ref_update alpha` が出会った場合、family match と同時に、引数同士を整合させる普通の型制約も生成する。

## effect 注釈の意味

effect 注釈は、表層 row を説明すると同時に、高階境界を越えて何を handler へ見せるかを決める。
ここで重要なのは、注釈の省略と `[_]` が同じ contract ではないことである。

| 注釈 slot | 内部的な意味 |
| --- | --- |
| 高階 callback 境界で注釈なし | 新しい capture contract を与えない。callback 由来の effect は空の可視性 evidence で守られうる。 |
| 高階 callback 境界の `[_]` | surface contract。その境界で推論された表層 row を見せる。 |
| 反変な computation 位置の `[console]` | capture contract。`console` だけを内側 handler に見せる。 |
| 共変な result 位置の省略または `[_]` | escape filter を足さず、row を open なままにする。 |
| 共変な result 位置の `[console]` | 外へ出る effect が `console` だけであることを検査する。 |

wildcard row `[_]` は annotation placeholder である。effect row 型そのものの標準構文ではなく、
boundary を消すものでもない。`g: _ -> [_] _` のような callback result では、`g(x)` の普通の
表層 effect を受け取り側の計算へ意図的に見せる。これを書かない場合、callback 由来の effect は
hygienic に保たれ、`#id[Empty]` のような evidence 付きで表示されることがある。

共変位置の具体 effect 注釈は **filter** である。filter は static check であり、runtime marker でも
residual row でもない。check が登録された後、保存される solver weight からは消える。

handler に消費されてはいけない fresh internal residual は、概念的には `take(Empty)` で守る。
推論コアには、別個の protected variable set はない。

## 表示される型の stack evidence

stack id や pop count は推論 evidence であり、source-level の型構文ではない。ただし、
compiler-oriented な表示では、高階 scheme を説明するためにその evidence が残ることがある。
通常の API 文書として読むときは、値型と effect row の構造を中心に読む。

```text
alpha [undet; beta] -> [beta] alpha
```

これは「引数 computation は `undet` と residual effect `beta` を起こしうるが、handler が見えている
`undet` を消費した後は `beta` だけが残る」という意味である。residual `beta` は公開型の本物の一部であり、
表示ノイズとして消してよいものではない。

隠れるのは、その境界で `undet` を消費してよい理由を説明する weighted evidence の方である。

高階関数では、空の可視性 evidence 自体が推論 scheme の重要な一部になることがある。
概略的には、注釈なしの compose には次のような protected occurrence が必要になる。

```text
compose_plain :
  (alpha [gamma#u[Empty]] -> [delta] beta)
  -> (epsilon -> [gamma#u[Empty]] alpha)
  -> epsilon
  -> [delta#u] beta#u
```

`#u[Empty]` は新しい effect family ではない。その occurrence の `gamma` は boundary `u` で
subtract できない、という証拠である。`g(x)` の表層 effect を `f` に意図的に見せたい場合は、
programmer が contract を書く。

```yulang
our compose(f, g: _ -> [_] _, x: [_] _) = f g(x)
```

その場合、公開型の形は普通の row-polymorphic compose として読める。

```text
compose_surface :
  (alpha [gamma] -> [delta] beta)
  -> (epsilon -> [gamma] alpha)
  -> epsilon
  -> [delta] beta
```

### data-position function の private evidence

標準ライブラリには、data value の中に effectful function を保持する抽象化がある。local reference が
代表例で、公開される `ref` value の内部には、返り effect に `ref_update` が関わる関数がある。

solver は、この保存された関数の latent return-effect tail を private evidence として扱い、
ordinary residual row だけを公開型へ projection する。そうしないと、synthetic field getter 経由で
`AllExcept(ref_update ...)` のような内部 stack id が public scheme に漏れてしまう。

公開型には、たとえば ref update なら次のような ordinary row だけが出るべきである。

```text
ref(e & b, a) -> (a -> [b] a) -> [e, b] unit
```

変数名そのものは重要ではない。重要なのは、保存された関数の hygiene を支える private stack evidence
ではなく、普通の residual row が public scheme に出ることである。

### replay の停止性は型等式ではない

solver は subtype graph の bounds を、正確な directed label 付きで replay する。
「pop が 1 個でも複数個でも同じ」という surface rule は使わない。

停止性のため、同じ endpoint、同じ subtract id、同じ effect family で同じ static boundary を
再訪する bound は、bounds table の保存時に subsume できる。これは同じ replay cycle を永遠に
回さないための実装規則であり、ユーザーに見える型の簡約規則ではない。

## 実行時の見方

specialize 後の runtime は、row 文字列から hygiene を推測して復元することはできない。関数値、thunk、
構造値は、実行される前に handler 境界を越えて移動しうる。

そのため runtime は、値と一緒に guard marker を運ぶ。概念的には、この marker が推論重みの実行時版である。

- 推論では、どの handler 境界がどの effect family を消費してよいかを決める。
- 実行時 marker は、実際に effect が発生したときの handler search に同じ境界を守らせる。

filter は runtime marker にならない。solver が静的に検査する。

## まとめ

Yulang の現行 effect 推論は、次の分担で成り立つ。

- 普通の value type と effect row は subtyping で推論する。
- handler hygiene は directed weighted inequality `T @L <: @R U` で表す。
- `catch` は row head から `H ∩ Common(L)` だけを引く。
- 右側 pop は head を見せるために使わず、residual tail へ運ぶ。
- handler があるからといって、未知 row を勝手に開かない。
- residual row variable は公開型の一部であり、黙って消さない。
- `#id[Empty]` のような空の可視性 evidence は、その row occurrence がその boundary で
  subtraction から守られている証拠であり、新しい effect ではない。
- data value に保存された effectful function の private stack evidence は、ordinary public row へ
  projection してから表示する。
- replay-cycle subsumption は solver の停止性規則であり、公開型の等式ではない。
- specialize 後は runtime guard marker が同じ hygiene を保つ。

これにより、表示される型は普通の row 型に近く保ちながら、内側 handler が呼び出し元の effect を
勝手に奪うことを防いでいる。
