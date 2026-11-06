# list literal / spread の未決定の問い（2026-11-06）

選択肢と推奨は仕様の決定ではない。推奨を先頭に置く。
回答に依存しない、解決済みの有限 list 値の構築・評価順・型安全性を先に進める。

## Q13. list spread の対象は list だけか、任意の Fold か

状態: **回答済み(2026-11-06): B**(ユーザー: 「Bだねえ……」。推奨Aと違う答え)。list spread の対象は任意の `Fold` 値。要素は走査順に新しい list へ入る。無限の Fold なら構築は終わらない。`spec/03-expressions.md` 3.1に反映。以下は質問の記録。

`spec/03-expressions.md` 3.1 は `[1, ..xs, 3]` を認める。
`spec/03c-control.md` 3c.1 は `for` の対象を任意の `Fold` とするが、
その規則を list spread にも適用するとは書いていない。

例（意味を問うための表記。parser/oracle 実行結果ではない）:

```yulang
my a = [0, ..[1, 2], 3]
my b = [0, ..(1..2), 3]
// Fold を実装するユーザー型 bag について [0, ..bag_value, 3] は許されるか
```

- **A（推奨）:** list spread の直接の対象は list とする。
  `Fold` 値は、明示的に list を作る処理を経てから spread する。
  source の対象型と既存 nominal list の要素型をそのまま照合できる。
- **B:** 任意の `Fold` 値を許す。spread はその走査順で要素を新しい list へ入れる。
  `for` と同じ role 解決・辞書・effect を接続し、無限 Fold なら構築が終わらない。

影響する義務: list spread の source 型判断、role 制約の生成、辞書選択、
spread の effect 行、`Fold` 走査から list 構築への翻訳、有限性を仮定しない進行・停止の区別。

この回答に依存しない範囲: operand が既に有限の list 値を返すと解決された核で、
任意の位置・任意個数の spread を書いた順に一回ずつ評価し、得た有限列を順に連結する。
この限定は source が A を選んだという仮定ではなく、どちらの案にも共通する実装層である。

## Q14. 既に型が決まった list を spread した要素へ、保留 cast 境界を新設するか

状態: **未回答**。

`spec/06-roles.md` 6.5 は、型が決まった nominal list の型引数へ cast を通さず、
list literal の各要素には構築位置の保留境界を置くとする。
spread が既存 list の値を新しい literal へ取り込むとき、その各値を「literal の各要素」
という新しい境界に数えるかは明示されていない。決定 25 を広げて採用しない。

例（意味を問うための表記。parser/oracle 実行結果ではない）:

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
my ids: list user_id = [user_id { raw: 1 }]
my numbers: list int = [0, ..ids, 2]
```

- **A（推奨）:** 既存 list を spread する部分は、既に確定した要素型のまま取り込む。
  spread で取り込む各要素へ新たな保留境界を自動生成しない。
  この例は `ids` の要素型と構築先の要素型が合わず拒否する。
  既存 nominal 値の内部を暗黙に走査して変換しない規則をそのまま保てる。
- **B:** 新しい list literal へ取り込まれる各要素に、新たな保留境界を置く。
  この例は新しい `numbers` を作る過程で各 `user_id` を `int` へ変換し、`ids` 自体は変更しない。
  source の一つの spread 位置から実行時の要素数ぶんの純粋な変換を発生させる。

影響する義務: list literal の弱変数制約、spread から保留境界の位置を生成する規則、
`NominalConstructions.finish` の静的siteと動的要素数の対応、
既存 nominal list の不変性と新規literalのcast挿入の境界、Rust oracle の変換回数。

この回答に依存しない範囲: 明示的に選ばれた純粋な変換コードを持つ通常の要素位置と、
既に構築先の要素型を満たす有限 list の spread を扱う。
spread の内部へ新しい変換を暗黙に挿入する source 規則は作らない。
これは B の source lowering を拒否すると決定した意味ではなく、その未決定の工程を
有限list構築kernelの外に残すという境界である。
