# C455: 実 record field を一歩ずつ読む G04

- C443 G04、I-83/I-85、spec §6.3（片付いていない出力からしか分からない head を開かない）と K2 の非変数 pattern の実検査位置。C412 は閉じた二段 record、可視一候補、元 where 一つ、出力なしの最初の field まで。G03b は触らない。
- 実 source: call-site の全可視リストが本当に一つ、元宣言の head/where そのもの、既存の役割・kind/constructor・識別子・scope・descent を検証。閉じた record pattern について depth を燃料で上限化せず、terminal binder より先まで勝手に降りない。元 root は実 point。各 proper prefix は original `Origin` の authored record と同じ actual raw row の所有者を読み、現在位置からその owner への raw Alias を検証する。未完 output の行だけで先へ展開しない。
- 独立な active trail: 読んだ元 pattern の見える field（非変数を調べる pattern 側の枝）と actual ordinary record field の一致、prefix は raw K2 でないこと、次の実 logical site。末端は実非変数位置に到達したあと、その同じ raw site が K2。末端自身の head を先に読む必要はない。変数捕獲や record tail は検査位置ではない。親 root 自身が循環ならこの内部 field 規則ではなく旧 root K2。
- Wire は実 row index, origin index, alias/field path, prefix escape, terminal raw closed path の有限データ。報告は親の完全な occurrence・候補 ID・元 field path・実 terminal name と K2、出力/where 選択なし。既存 C454 入口に additive previous arm で繋ぎ全旧 Bool 不変。正確な独立局所報告に有限 wire、受理したとき同一 State のモデルで実 source 証拠と診断。未証明な構文範囲は明示する。
- 対照: arbitrary-depth legacy closed spine (minimum depth 3) + actual owner alias, 動かした row/location や別の raw cycle だが実到達していない field、変数または early-cycle の prefix、未知/未完 provenance。巨大な環境や全体的な停止性、一般の否定完全性、G05 は対象外。
