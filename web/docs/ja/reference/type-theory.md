# 型推論の理論

このページは、Yulang の型推論で effect と handler がどう扱われるかを、リファレンス向けにまとめる。

細かい実装名よりも、次の疑問に答えることを目的にしている。

- effect row は普通の subtyping とどう関係するのか。
- handler はなぜ effect を消せるのか。
- 関数引数から出た effect を、内側の handler が勝手に捕まえないのはなぜか。
- その内部情報が、なぜ hover や Types pane には出ないのか。

## 前提: 式は値型と effect row を持つ

Yulang の式は、値の型と effect row を持つ。

```text
e : A ! ρ
```

これは「式 `e` は値 `A` を返し、その途中で effect row `ρ` の effect を起こす可能性がある」
という意味である。

Yulang の表面表示では、この 2 つをまとめて次のように書く。

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

effect row もこの制約 graph の中を流れる。

```text
[console] str <: [console; e] str
```

このように、具体的な effect は open row に入れられる。handler が effect を消した後の残りも、
同じ graph の中で通常の row として流れる。

## Handler は effect row から effect を取り除く

`catch` は、内側の computation が起こす effect のうち、arm で処理する effect を取り除く。

```yulang
act console:
    our read: () -> str

our run_console(action: [console; e] 'a): [e] 'a = catch action:
    console::read(), k -> run_console(k "42")
    v -> v
```

ざっくり言うと、`action` の effect row が `[console; e]` なら、`catch` の外側では `console` が
消えて `[e]` になる。

ただし、この説明にはまだ足りない部分がある。高階関数では「その effect はどこから来たのか」
が重要になる。

## 問題: 引数由来の effect を勝手に捕まえてはいけない

次のような関数を考える。

```yulang
my compose f g x = f(g x)
```

`g x` は何か effect を起こすかもしれない。もし `g` が `last` effect を起こすとしても、
`f` の内部にある `last` handler がそれを勝手に捕まえてはいけない。

直感的には、`g` の effect は `compose` の呼び出し元が持ち込んだものだからである。`f` の中に
handler があるからといって、別の引数から来た effect まで吸い取ると、高階関数の意味が不安定に
なる。

これを Yulang では handler hygiene と呼ぶ。

## 境界: 何を handler から見せるか

関数引数や thunk 由来の computation を handler の内側で実行するとき、Yulang は boundary を
置く。

boundary は、その effect row のうち、どれを今の handler から見えるままにするかを持つ。

| 注釈 | boundary の意味 |
| --- | --- |
| 注釈なし | 何も見せない。引数由来の effect は内側 handler から隠れる。 |
| `[_]` | 表層にある effect は見せる。 |
| `[console]` | 表層の `console` だけ見せる。 |

この「見せるもの」を実装では `keep` と呼ぶ。

重要なのは、`[_]` でも boundary 自体は消えないことだ。`[_]` は「今すでに表層にある effect を
見せる」という意味であって、奥に隠れていた effect まで表層へ戻すわけではない。

## Handler matching は subtyping graph の横に置く

handler が effect を消す規則は、普通の row subtyping だけでは表しにくい。

理由は、`actual` がまだ型変数のときに、次のような推測をしてはいけないからである。

```text
handler_match(ε, Surface, {console}, ρ)
```

ここで `ε` は未知の effect row である。この時点で、`ε` の表層に `console` があるとは分からない。

したがって、推論器は次のように row を発明しない。

```text
ε = [console; rest]
ρ = [rest]
```

代わりに、普通の subtyping graph の横へ hidden constraint を置く。

```text
handler_match(actual, keep, handled, residual)
```

これは「`actual` のうち、`keep` によって今の handler から見えていて、かつ `handled` に含まれる
effect だけを消すと `residual` になる」という関係である。

`actual` の表層が後から具体的に見えたら、その時点で解く。

```text
actual   = [console, state]
keep     = Surface
handled  = {console}

residual = [state]
```

一方、最後まで `actual` が未知の row なら、`handler_match` は hidden evidence として残る。

## なぜ型表示に出さないのか

`handler_match` は型ではない。`[; e]` のような boundary marker も公開型ではない。

公開型に出るのは、普通の value type と普通の effect row だけである。

```text
α [console; e] -> [e] α
```

hidden constraint は、次のような情報である。

```text
この computation が handler に入るとき、どの effect を見せてよいか
```

これは「値が何型か」や「外へ残る effect row が何か」とは別の情報である。だから hover や
Types pane では通常表示しない。

ただし、hidden constraint が具体 row から解けた場合、その結果の residual は普通の row として
表示に反映される。

```text
internal:
  handler_match([console, state], Surface, {console}, ρ)
  ρ = [state]

public:
  [state] α
```

表示しないのは `handler_match` そのものであって、解けた結果まで捨てるわけではない。

## 表層型が同じでも hidden evidence が違う例

次の 2 つは、表層型だけを見ると同じ形になることがある。

```yulang
my compose_plain f g x = f(g x)
my compose_surface f (g: _ -> [_] _) x = f(g x)
```

表層型は、どちらもおおむね次のように見える。

```text
compose_plain   : (α [γ] -> [δ] β) -> (ε -> [γ] α) -> ε -> [δ] β
compose_surface : (α [γ] -> [δ] β) -> (ε -> [γ] α) -> ε -> [δ] β
```

しかし hidden evidence は違う。

```text
compose_plain:
  g 由来の effect は内側 handler から隠す

compose_surface:
  g 由来の表層 effect は内側 handler に見せてよい
```

表層型は「`g` の effect がどこへ流れるか」を表す。hidden evidence は「その途中の handler が
どの effect を捕まえてよいか」を表す。役割が違うので、表層型だけでは区別が付かないことがある。

## 実行時の見方

実行時には、effect row を毎回書き換えない。代わりに、handler search のときに boundary を見る。

概念的には、effect が発生したときに内側から外側へ handler を探す。

```text
perform console
  -> boundary があれば「この handler から見えるか」を判定
  -> 見える handler だけが捕捉候補になる
```

未注釈引数由来の effect は、内側 handler から見ると隠れている。対応する boundary の外側へ出ると
また普通の effect として見える。

このため、型推論で「row の全 effect の番号をずらした型」を公開する必要はない。推論では
hidden constraint、実行時では boundary evidence として扱えばよい。

## まとめ

Yulang の effect handler hygiene は、次の分担で成り立つ。

- 普通の value type と effect row は、通常の subtyping graph で推論する。
- handler が何を消せるかは、`handler_match` という hidden constraint として graph の横に置く。
- 未知の row から effect entry を発明しない。
- `handler_match` は型表示に出さない。
- 解けた residual だけを普通の effect row として表示に反映する。
- 実行時には boundary evidence を見て、捕捉してよい handler だけを選ぶ。

この設計により、表層型は普通の row 型のまま保ちつつ、高階関数の effect hygiene を守れる。
