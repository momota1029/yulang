# 要求順序と constructor 観測に残る契約

状態: **問い。未回答部分は言語仕様の変更として扱わない。**
日付: 2026-11-07。決定46・47、既存 Q2 の案1、Q3 の独立 `exactEmpty` を前提にする。

## Q4. constructor の payload 内でも mask を観測するか

**問い:** 要求の文法の `mask` は、pair/field/tag の子に入った後でも独立に使えるか。

例: `P = required 7 bottom`、`B = bottom` とする。既存 data 観測では unmasked な `P` と
`B` は等しいが、mask `[7]` の後は `P` だけが records を許す。
現在の `PresenceMaskedCoalescing` は root の全 mask を調べ、variant の子は unmasked に読むため、
`variant 11 P ≤ variant 11 B` は成り立つが、子の全 mask 比較 `P ≤ B` は成り立たない。

`PresenceConstructorObstructions.MaskedPayload` の `input_model` が4-node入力の独立解を構成する。
`no_closed_cache_preserves_model` は、この解を保存する現行 `Closed` cache が一つもないことを示す。
`no_exact_closed_alternatives` は、同じ graph 上の任意の有限 cache 列に対して完全性を否定する。
これは、別の観測・obligation 表現や graph を拡張する手続きまで否定する定理ではない。

選択肢:

1. **推奨:** 要求の mask を構成子の内部でも許す。新 `ProducerLe` の観測を文脈内まで閉じ、
   子の要求比較を親の要求比較から回収できるようにする。既存の root-mask data モデルは別の投影として残す。
2. root-mask data モデルの観測をそのまま保持し、cache に「子を unmasked に比較する」辺と
   「root を全 mask で比較する」辺を別々に持たせる。coalescer と回収定理もこの区別に合わせて構成する。

**仮の作業前提:** 既存の data 型判断・`Models`・`Closed` は変更しない。
現時点の constructor-bound 定理はどちらの選択にも依存しない。
新たな要求モデルにおける mask の具体的解釈は、その定義と依存する定理の前提に明示する。
選択肢1の最終採用や、全 source への接続をこの問いの記録だけで済ませない。
