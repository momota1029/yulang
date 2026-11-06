# list literal / spread の未決定の問い（2026-11-06）

選択肢と推奨は仕様の決定ではない。推奨を先頭に置く。
回答に依存しない、解決済みの有限 list 値の構築・評価順・型安全性を先に進める。

## Q13. list spread の対象は list だけか、任意の Fold か

状態: **未回答**。

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
