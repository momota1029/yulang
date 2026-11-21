# C332: 正規化した実 pattern と元 RHS から入れ子の Read を計算する

I-56/I-58/I-59。C331 は任意個の binder field を生成したが、内側に構造を持つ field の Read 自体を独立には生成していなかった。今回は元の正規化・translate を通った式を reify し、actual/lower/upper の read をその syntax に沿って計算する。raw 複合 payload は候補を知らずに読み、名前を開く場合に限り支持付きの保存済み行と alias を確認する。nominal の子だけ actual mode にし、record は同名の隠れた出現を取り除き、残余を二重に参照しても推測しない。

これは有限の局所 syntax の計算で、飽和の停止や「読めないから拒否／保留」を意味しない。現状態の独立した候補・支持・K2 と固定書込み照合は別である。意味を変える新しい優先順位は導入しない。
