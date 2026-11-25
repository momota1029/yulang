# C414 / I-74 C06 / X4 前半の検証

| 要件 | 実装と検証 |
|---|---|
| (a) 元の宣言判断の追加 | `OpenTail414.R6` は R5 の選択を変えず、元の open record、実 int field、全候補の実 singleton head と同じ binder の where、tail に普通行・alias・区間・origin・native 行・route がない範囲で `other .pending []` のみ追加。`dictionary_sound_R6` は元の全称と固定 `DictionaryEvidence`。 |
| (b) 実行時の有限な証人 | `OpenWire` は実 origin の添字と raw 根の安全証明書のデータだけ。入力の型、tail、候補、where、保留は証人の自己申告でなく実入力から取り出す。`check` は pending/pending/書込なしの正確な報告だけ true。 |
| (c) 健全性を保持 | `OpenTail414.check_sound` は同じ入力の実導出の報告、同じ State のすべての適合モデルでの元の意味。R5 の checker 分岐は定義的にそのまま、成功した選択の木・固定書込みは保存する。 |
| K2 優先 | 実入力の alias は恒等で、raw の構造閉路はない。正規化した raw graph だけを見て open row を空とみなしていない。元構文上の根→field/尾への辺も復路がないことを別に証明。実際の根 K2 を持つ実行対照では旧 API が拒否を確認し、新規 pending は false。 |
| 検査の限界 | 単一の点入力、open record + int の二行、実候補一つ、その同じ binder を使う where 一つ、出力なし。通常の head/where の正規化後に書かれたサイズと出現回数を検証した。任意に同名 field を含む tail を代入する旧十分条件はこの例に使えず、引き算・任意代入・子作成を加えていない。既知 tail・別の候補集合・区間・route・native など別ケースで false は言語の診断ではない。 |
| 実対照 | X4 は真に pending、元の同じ State が空 tail と field を持つ観測上別の tail の両方に適合。両モデルで同じ保留の証拠。実 tail と宣言 binder の名前は別。origin の添字を動かしても同じ元要求・宣言・節・field・tail、別証人はそれらを書き換えられない。 |

コードの厳密な再検証ピン: `e33c9f3604b6777b070a899964fd15effcf8866b`（Lean tree `a216e11fef40b41eae01cd3bf3605bf97667edca`）。根拠は [仕様 6.3](../../spec/06-roles.md) 、適合例 X4 の前半。X4 後半の subtraction/residual は C07 に残す。
