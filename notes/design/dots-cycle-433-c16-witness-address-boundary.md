# C433: 同じ witness の元 receipt は一意、State 単位の内部住所は別

元の公開 R16 を変更せずに二つの事実を確認した。

1. 任意の同じ State・元 request・同じ `AssociatedWire432` が二つの report を通すなら、二 report は完全に同じ。元の data-only replay が返す packet と exact report comparator から出る。
2. 一方、同じ元 State/request の中に、同じ元 child の RHS に適合する二つの**完全に整合した**行束（child target 4 と 14）を保持した対照では、各 witness が異なる元 receipt 列を通す。公開親 target 12 と選択辞書は同じで、どちらも同じ適合モデルに正しい。witness と receipt を交差すると両方とも false。元の selector の固定 report 比較を値の一致で弱めていない。

従って一意性は「その実 witness での exact readback」に限る。State がただ一つの内部 lexical target を強制すること、solver が特定の target に割り当てること、別 address を同一視して report を受理することは主張していない。C16 の公開分岐、言語規則、C の計上に変更なし。
