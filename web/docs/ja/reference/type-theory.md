# 型推論の理論

このページは、Yulang の型推論が effect と handler をどう扱うかを、公開
reference 向けにまとめる。完全な solver 仕様ではなく、CLI、playground、language server が出す
型を読むための地図である。

重要なのは、handler hygiene を今は独立した hidden `handler_match` 関係として説明しないこと。
現行実装では、同じ考えを subtype solver の中で **stack 重み**付き不等式として表す。

## 式は値型と effect row を持つ

Yulang の式は、値の型と effect row を持つ。

```text
e : A ! ρ
```

これは「式 `e` は値 `A` を返し、その途中で effect row `ρ` の effect を起こす可能性がある」
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

例えば、ある場所が `int` を期待していて、実際の式も `int` ならそのまま通る。branch などで
複数の可能性が残る場合は、推論結果に `α | int` のような union が出ることもある。

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

## stack 重み付き row

推論器の内部では、型に stack 重みを付けることがある。

```text
stack(T, @S)
```

これは source language に `stack` という型コンストラクタがあるという意味ではない。どの handler
境界が、どの effect family を引いてよいかを覚えるための内部表現である。

stack entry は、小さな予算のように読める。

```text
pop(n)[H1, H2, ...]
```

- `[console]` のような push は「この境界では `console` を handler に見せてよい」という予算である。
- `pop(n)` は、その予算を関数や thunk の境界を越えて戻す。
- `floor` は、すでに消費した effect を覚える。これがあるので、同じ effect を後から何度も発見して
  引き直すことがない。

順序は重要である。後から来た `pop` は前に積まれた entry を消費できるが、未対応の `pop` の後ろに
push された entry が、その古い `pop` をなかったことにはしない。そのため、推論器は重みを単なる集合ではなく、
順序付き stack entry として持つ。

## 重み付き不等式

subtype solver は、左右に重みを持つ型不等式を扱う。

```text
T @L <: @R U
```

`stack(T, @S)` に当たったら、`stack` wrapper を型から剥がして重みへ移す。

```text
stack(T, @S) @L <: @R U
=> T @(@S + @L) <: @R U

T @L <: @R stack(U, @S)
=> T @L <: @(@S + @R) U
```

普通の variance はそのまま効く。関数の引数位置は反変なので、そこへ入ると左右の重みが入れ替わる。
返り値位置は共変なので、重みの向きはそのままである。

`int` や `bool` のような具象 terminal 型では、重みは観測されないので落としてよい。関数型、record、
tuple、effect row、型引数の中では、後で nested row の subtraction に届く可能性があるため重みを流し続ける。

## `catch` はどう effect を引くか

`catch` が effect 集合 `H` を処理するとき、推論器は scrutinee の row を次の形で見られるかを調べる。

```text
α @L <: @R [H; β]
```

左右の重みが空なら、これは普通の row 制約である。推論器は subtraction 予算を勝手には作らない。

重みがある場合だけ、実際に見えている部分を計算する。

```text
W = L + R
U = H ∩ common_stack(W)
```

- `U` が空なら、この handler はその row から何も消費できない。residual row はそのまま残る。
- `U` が空でなければ、`α` が `[U; γ]` を持ちうることを登録し、重みから `U` を引いて、
  residual 変数 `γ` を `β` へ流す。

同じ subtraction slot には同じ residual 変数を再利用する。これにより、recursive handler が
fresh な tail を無限に作り続けることを避ける。

型引数を持つ effect family は family path で突き合わせるが、引数は捨てない。`ref_update int` と
`ref_update α` が出会った場合、family match と同時に、引数同士を整合させる普通の型制約も生成する。

## effect 注釈の意味

effect 注釈は、公開 row を説明すると同時に、高階境界を越えて何を handler へ見せるかを決める。

| 注釈 | 内部的な visibility |
| --- | --- |
| effect 注釈なし | 呼び出し元由来の effect を内側 handler が消費する予算を与えない。 |
| `[_]` | 表層で見えている effect を見せる予算を与える。 |
| `[console]` | `console` だけを見せる予算を与える。 |

wildcard row `[_]` は annotation placeholder である。effect row 型そのものの標準構文ではなく、
boundary を消すものでもない。あくまで「いま表層に見えている effect を露出してよい」という意味である。

このため、表層型がよく似ている 2 つの高階関数でも、内側 handler が捕まえてよい effect は違うことがある。

## 公開型には stack 重みを出さない

stack id、floor、pop count は推論 evidence であり、source-level の型構文ではない。通常の hover や
Types pane には、普通の value type と普通の effect row だけを出す。

```text
α [undet; β] -> [β] α
```

これは「引数 computation は `undet` と residual effect `β` を起こしうるが、handler が見えている
`undet` を消費した後は `β` だけが残る」という意味である。residual `β` は公開型の本物の一部であり、
表示ノイズとして消してよいものではない。

隠れるのは、その境界で `undet` を消費してよい理由を説明する weighted evidence の方である。

## 実行時の見方

specialize 後の runtime は、row 文字列から hygiene を推測して復元することはできない。関数値、thunk、
構造値は、実行される前に handler 境界を越えて移動しうる。

そのため runtime は、値と一緒に guard marker を運ぶ。概念的には、この marker が推論重みの実行時版である。

- 推論では、どの handler 境界がどの effect family を消費してよいかを決める。
- 実行時 marker は、実際に effect が発生したときの handler search に同じ境界を守らせる。

したがって handler hygiene は、型推論だけでなく VM lowering にも関わる。

## まとめ

Yulang の現行 effect 推論は、次の分担で成り立つ。

- 普通の value type と effect row は subtyping で推論する。
- handler hygiene は `stack(T, @S)` と重み付き不等式 `T @L <: @R U` で表す。
- `catch` は、現在の stack 重みで見えている effect family だけを引く。
- handler があるからといって、未知 row を勝手に開かない。
- residual row variable は公開型の一部であり、黙って消さない。
- stack 重みそのものは内部 evidence として隠す。
- specialize 後は runtime guard marker が同じ hygiene を保つ。

これにより、表示される型は普通の row 型に近く保ちながら、内側 handler が呼び出し元の effect を
勝手に奪うことを防いでいる。
