# C417: X6 後半の二候補

I-74 C09 のみ。開始時 `integration/m1-final` は `ad65248e70b70ca116703701c55bbb220c5e21c6`、
Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。仕様 6.3 は、同じタグの
`impl R (:{tick 'a,tick 'b})` で二変数とも実 payload 全体を捕捉し、
`impl R (:{tick int})` も同じ実入力に当たるとき、選択せず曖昧とする。

元の一点要求、authored variant 行、元の self-join 行と実 integer 行を
C416 と同じ State から読む。単独候補の C416 読取器を二回呼ぶことはしない。
両宣言をその実 ordinal で別々に読み、role/署名/where 無し/出力無しを確かめ、
実可視リストがこの異なる二宣言のどちらかの順でちょうど尽きることを確認する。
plain では元の join 両腕にそれぞれ実 payload を捕捉し、ground では
宣言表の primitive int と、同じ variant 行の同じ実 payload の int 行と照合する。
二つの `SourceHead` は同じ State/Request で作り、任意の同じ fitting model で成立する。

生グラフの K2 は根と、ground が本当に降りる実 payload で別に除外する。
proof-only な `Visits` は保管しない。wire の有限色と全元行の検査から
根 alias を経た同タグの実観測先が一致することを証明する。
曖昧の報告に選択や出力を付けない。既存の入口は引き継ぐ。

ここは前記 scope のみ。実 self-join 不在や追加候補、構文の違いを
`false` にしても、言語の拒否とはしない。Rust/一般の完全性/停止性は対象外。
