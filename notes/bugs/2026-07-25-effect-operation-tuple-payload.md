# 効果操作のタプルペイロード（当初の記述は誤り・2026-07-26 全面改訂）

発見日: 2026-07-25
改訂日: 2026-07-26
状態: **解決済み（2026-07-26、`60922f69`）。** 当初の主張は誤りで、実際の欠陥は
下記「本当の残存問題」だった。それも同日に修正済み。

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


## 解決 2026-07-26

`60922f69` で閉じた。

### 原因

Evidence VM が Tuple→Tuple の `Coerce` を `Alias` に潰していたため、タプルの**要素ごとの
adapter が挿入されなかった**。適応されないままの thunk が `IntAdd` の `expect_int` へ届き、
`non-int primitive argument` になっていた。

単独の thunk payload が動くのは、既存のトップレベル adapter 経路を通るためである。
adapter がタプルの一段下まで届いていなかった、というだけの差だった。

根本原因は効果に固有ではなく、**Tuple→Tuple の runtime boundary adaptation の欠落**である。
効果操作を通じて表面化したのは、その経路が whole-tuple の coercion を作るからにすぎない。

### 修正

Tuple の coercion を runtime expression として保持し、要素ごとに適応する。

変更の大半は意味論ではなく配線である。要素を強制する途中で効果によりサスペンドしうるため、
再開可能な継続フレームが要り、それを Evidence VM の継続ライフサイクル全体——統計、走査、
snapshot / delta replay、direct-tail / generic request、resume dispatch——へ通す必要があった。
mono runtime 側は `continue_with` が既にサスペンドを包むため、はるかに小さい変更で済んでいる。

### 検証

```console
$ yulang --std-root lib --no-cache run --print-roots <repro>
L
R
run roots [5]
```

効果を含まない同じ形は両バックエンドで一致する（`run roots [5]`）。
`println` を含む形が mono interpreter で動かないのは、interpreter が host 効果を扱わないという
既存の境界であり、本件とは無関係
（`notes/design/2026-07-25-test-facility-design.md` §5.5）。

evidence-vm 162 / mono-runtime 27 / infer 961 / specialize 150 / parser / `--test cli` 152 /
contract 232 / fmt、すべて通過。

### `assert_eq` について

これが `assert_eq` を保留していた理由だったので、障害は解消した。
実装は `notes/design/2026-07-25-test-facility-design.md` §2.5 の承認済み設計どおりに進めてよい。
