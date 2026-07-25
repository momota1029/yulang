# 効果操作のタプルペイロード（当初の記述は誤り・2026-07-26 全面改訂）

発見日: 2026-07-25
改訂日: 2026-07-26
状態: **当初の主張は誤りだった。** 実際に残る問題は下記「本当の残存問題」だけ。

## 訂正

初版は「効果操作のペイロードがタプルだと扱えない」と書いたが、**これは誤りである**。
再現に使ったプログラムの綴りが間違っていた。

```yu
probe::pair(2, 3)     -- タプルではない。カリー化された2引数適用 ((pair 2) 3)
probe::pair (2, 3)    -- こちらがタプル1引数
probe::pair((2, 3))   -- こちらもタプル1引数
```

`f(a, b)` は `f` にタプルを渡すのではなく、`f` を `a` に適用してから結果を `b` に適用する。
効果操作でも同じで、最初の適用で効果が発生し、payload は `a`、残りの適用は継続の中に入る。

これが初版の観測をすべて説明する。

- destructuring の腕が一致しない → payload が `2` であってタプルではないため
- 丸ごと束縛すると引数が崩れる → `p = 2`、`k = 継続`。`k(99)` の後に残った適用が `99(3)` になり
  `not-callable 99` が出る

## 正しく書けば動く

```yu
act probe:
    pub pair: (int, int) -> int

my h(x: [_] _) = catch x:
    probe::pair (a, b), k -> h: k(a + b)
    value -> value

h: probe::pair (2, 3)
```

```console
run roots [5]
```

丸ごと束縛も動く。

```yu
    probe::pair p, k -> h: k(99)
```
```console
run roots [99]      -- probe::pair((2, 3)) に対して
```

したがって**タプルペイロード自体は正常に機能する**。

## 本当の残存問題: 関数値を含むタプル

タプルの中身が関数（thunk）の場合だけ、実行時に落ちる。

```yu
act probe:
    pub two: (() -> [_] int, () -> [_] int) -> int

my h(x: [_] _) = catch x:
    probe::two (l, r), k -> h: k(l() + r())
    value -> value

h: probe::two (\() -> { println "L"; 2 }, \() -> { println "R"; 3 })
```

```console
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report
```

単一の thunk ペイロードは正常に動き、ハンドラが強制すれば thunk 内の効果も実行される
（`lib/std/testing.yu` の `assert` が実例）。落ちるのは**タプルに関数値を入れた場合**である。

これが `assert_eq`（`notes/design/2026-07-25-test-facility-design.md` §2.5）を保留している
実際の理由である。承認済み設計は 2 つの遅延オペランドをタプルで渡す形であり、この経路を通る。

## 着手前に確認すること

- `non-int primitive argument` はどの段階で出るか。specialize か control-IR lowering か VM か。
- タプル内の関数値が、スカラのタプルと何が違う扱いを受けているか。
- 単一 thunk が動くのに、タプル内 thunk が動かない差はどこか。

## 副産物として発見された別の欠陥

この調査中に、無関係な型健全性の穴が見つかった。
`notes/bugs/2026-07-26-structural-argument-mismatch-accepted.md` を参照。

## 経緯についての注記

初版は Claude が書いた。再現プログラムの `f(a, b)` を「タプルを渡している」と誤読したまま、
4 つの判別実験を組んで「タプルが原因」と結論した。判別実験どうしは整合していたが、
全部が同じ誤った綴りを共有していたため、誤りが打ち消されずに残った。

Codex（gpt-5.6-sol, xhigh）の診断で綴りの誤りが判明し、Claude が再検証して改訂した。
