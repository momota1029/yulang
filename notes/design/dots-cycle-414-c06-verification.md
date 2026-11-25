# C414 / I-74 C06 / X4 前半の検証

| 要件 | 実装と検証 |
|---|---|
| (a) 元の宣言判断の追加 | `OpenTail414.R6` は R5 の選択を変えず、元の open record、実 int field、実 role 宣言・有効な role 表、全候補の実 singleton head と同じ binder の where、tail に普通行・alias・区間・origin・native 行・route がない範囲で `other .pending []` のみ追加。`dictionary_sound_R6` は元の全称と固定 `DictionaryEvidence`。 |
| (b) 実行時の有限な証人 | `OpenWire` は実 origin の添字と raw 根の安全証明書のデータだけ。入力の型、tail、候補、where、保留は証人の自己申告でなく実入力から取り出す。`check` は pending/pending/書込なしの正確な報告だけ true。 |
| (c) 健全性を保持 | `OpenTail414.check_sound` は同じ入力の実導出の報告、同じ State のすべての適合モデルでの元の意味。R5 の checker 分岐は定義的にそのまま、成功した選択の木・固定書込みは保存する。 |
| K2 優先 | 実入力の alias は恒等で、raw の構造閉路はない。正規化した raw graph だけを見て open row を空とみなしていない。元構文上の根→field/尾への辺も復路がないことを別に証明。実際の根 K2 を持つ実行対照では旧 API が拒否を確認し、新規 pending は false。 |
| 検査の限界 | 単一の点入力、open record + int の二行、実候補一つ、その同じ binder を使う where 一つ、出力なし。通常の head/where の正規化後に書かれたサイズと出現回数を検証した。任意に同名 field を含む tail を代入する旧十分条件はこの例に使えず、引き算・任意代入・子作成を加えていない。既知 tail・別の候補集合・区間・route・native・fallback arity のみで role 宣言がない場合 など別ケースで false は言語の診断ではない。 |
| 実対照 | X4 は真に pending、元の同じ State が空 tail と field を持つ観測上別の tail の両方に適合。両モデルで同じ保留の証拠。実際に完了した別需要から tail へ届く retained output も同名参照だけで、固定の残部をはじめて決める根拠にはならない。実 tail と宣言 binder の名前は別。origin の添字を動かしても同じ元要求・宣言・節・field・tail、別証人はそれらを書き換えられない。 |

コードの厳密な再検証ピン: `7e65e94347471a35428fa91c7a31d1f3c7d9052c`（Lean tree `0baabd2e36fb2ed89017867219848a6a9c28ee97`）。根拠は [仕様 6.3](https://github.com/momota1029/yulang/blob/87a10414e952d07b61376aa8b0c6dc45df54cfaf/spec/06-roles.md#L106-L109) 、適合例 X4 の前半。X4 後半の subtraction/residual は C07 に残す。

追加の厳密な回帰確認: 統合済み C408 を基準に、固定コミットから C409–C414 の対象モジュール 47 本、独立監査 35 本、追加 import 群を `Lean 4.35.0 --trust=0 -DwarningAsError=true` で照合・再生、終了コード 0。別のローカルの結合スモーク試験で新しい公開入口から旧 X12・X8・X9・X10・X11 両順・X4・raw 根 K2 の正例をすべて再実行し、誤報告と unsupported を含め `[true,true,true,true,true,true,true,true,false,false]`。これはこの掲載済み実例の回帰であり、全リポジトリのビルドや一般完全性ではない。
