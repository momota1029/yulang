# struct の field に出る全称量化（rank 2）

状態: ユーザーの決定（2026-11-07）の記録。署名: Claude (Sonnet 5.5)。
規則は `spec/04-types.md` 4.6 に追加した（`ref` の field は `run` だけで、`get` は `sub: r.run \a -> { return a; ... }` で作る。2026-11-07）: struct の型引数に無い型変数が field の型に出てきたら、その field の中で全称量化される。対象はユーザーが書く struct すべて。

例（ユーザーの例）:

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
```

## 何が起きるか

- 作る側: `'f` を rigid にして検査する（全称）。使う側: 取り出すたびに好きな `'f` で具体化（存在）。
- operation-local 多相（spec 5.x）と同じ量化の分け方。Lean では `EffectInference` / `RowInference` が、有限個の operation-local 型変数を呼出側で存在具体化・handler 側で rigid 検査する別モデルで証明している。共通の判断（`Common`）には B3 が統合を進めている最中で、まだ載っていない。
- ただし、operation の署名の中の変数と、struct の field の型の中の変数は別の場所にある。後者は「型の中に量化子がある」ことになる。

## Lean で足りないもの

- 現在の `Common.Ty` は、量化を束縛（scheme）の位置にしか持たない。型の中の `∀` が無い。field が `∀'f. ...` を持つ nominal 型を表すには、少なくとも次が要る。
  - nominal の field 表（宣言）に、field ごとの量化変数の列を持たせる。型本体の中に `∀` を入れる案は、型の等価・正則型・coalescing 全部に響くので避け、**宣言表の側に量化を置く**案を第一候補にする。
  - 構築の規則（rigid で検査）と射影の規則（具体化）。operation-local の規則からの流用を試す。
- 未決（Yulang のコードで違いが出る問い）:
  1. `∀` を持つ field を持つ struct 同士の比較。`ref 'e 'a` の `'e` が違う二つの値を、部分型でつなげるか。field の共変・反変・不変。
  2. 値制限・一般化との関係。多相 field を持つ値を `my` で束縛して、さらに一般化するか。
  3. role の解決。`impl R (ref 'e 'a)` の head は field の量化変数に触れない（nominal の型引数だけを見る）はず。確認する。
  4. lambda の引数の多相（`\f -> (f 1, f "a")`）は、これとは別。まだ決めていない。

## 次の一手

- 設計メモにしてから、B6（公開入口への統合）の前に、独立の目標（B7 仮）として Lean に載せるかを決める。
- 今走っている B3 には、この件を伝えない（スコープ外）。B3 の operation-local 全称 handler が閉じたら、その道具で足りるかを見る。
