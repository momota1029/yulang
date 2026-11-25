# C406: 今回追加した native root を本物の元出力として使う

一段目 `ScopedSource406.completed` の子・支持には C405 の木を再利用した。これを
C405 の古い head に変換せず、次の同一 State の lower 出力として読む。
同じ `ScopedSource406` と ordinal に依存する `ScopedOutputRead406` の後ろに、実出力
・元パス・固定先・比較・候補の元番号を明示する。有限な支持の鎖を作る場合も、同じ判定結果の
別の proof や一致した denotation を代用しない。新しい節ではこの単項共変 lower だけ。
複数候補の被覆、任意の native / ordinary form、任意の相互 where 再帰は範囲外。
