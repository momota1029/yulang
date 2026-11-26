# C447 — G00 の局所選択・保持を公開入口で往復させる

I‑82 / I‑81 §6。正本 integration/m1-final@ec31261851fafa06fa61b14776e9fd90c19b0742。C444–C446 の State、writer、宣言的規則と従来入口は不変。

- データ: 従来 witness の委譲と、元の authored origin の位置および raw K2 の有限順位・側表だけを持つ新 witness。宣言の番号・元 B6 木・kind と capture・元の要求の固定先・保持行・報告は同じ State から読む。
- 独立判断: C445 の LocalSelection。where 無し、可視候補一つ、元の混在 row/value nominal の一出力、元の固定先に対応する真正の singleton 保持、旧状態を壊さない保守的な fresh 条件。追加の global header/外部 escape/配置/check 成功を前提にしない。新しい言語規則を足さない。
- 実行版: 選ばれた元の宣言だけを C446 の selectedHeader で反映し、同じ raw K2 と ordinal/source/B6/固定先を検査する。旧 witness はすべてを旧 checker へ委譲。正しさは同一 State の全 FitsFull。
- 証明する外形: 全 p,r,w で checker=true なら同じ State の分類と、任意 m, FitsFull → 同じ exact report の証拠。全 p と独立 LocalSelection a で、a の辞書/元の出力列 a.report を受理する有限 wire が存在する。逆向き: 新分岐の check=true が返れば実際に読んだ同一 source と同一 report の局所導出が存在する。
- 対照: 元 slot 21 の真正保持は true、slot 22、既出 Int との連言、保持なしは false。独立に Checked な無関係の ground where 宣言を持つ C446 の反例で旧 witness の枝は false のまま、新分岐が同じ元報告を true にする。モデルのない状態を受理することで健全性を空虚にしない。
- typed retention の release や一般の raw 観測輸送、一般の R_full / NoFalseRejection、G01 以降は、この狭い G00 の定理とは別。
