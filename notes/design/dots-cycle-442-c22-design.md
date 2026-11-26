# C442 / C22 — row 引数を持つ関連型の元の固定先

正本 `integration/m1-final@fbbf227b2023e0da5d18d8f5c3826545f6b79e28`。C423 の C22 のみ。§6.1 の関連型本文、§6.3 の「選択した impl が等式を追加」、§4.6 の row/value 引数位置を組み合わせる。既存 spec にこの組合せそのものの例はない。検証対象は宣言済み mixed nominal と row/value の区別であって、rank-2 `run` の lowering ではない。

1. 元の `AuthoredBodyFrame393` とその declared occurrence、`Fin outputCount`、同一の B6 atlas entry および declared mixed constructor Use。row と value の異なる binder はそれぞれ当該 frame の実 slot で、元の RHS は `ref 'e 'a` の二引数順。元の `NamedMixedReceipt401.actualEquation` はどの同一モデルでも original target と `nominal key [inr row, inl value]` を返す。証明を入力する public wire は作らない。
2. それだけでは `I72.FixedTargets` ではない。現行 `fixedValueCode403` が row 付きの元の木をコード化できないことを確かめる。all-value nominal の表現否定を、変数・別由来の具体的混合値を表す値一般の否定と混同しない。
3. `Fits` の ordinary assignment、authored view、nativeSyntax を分離して、関係する行を見たことと output target に実等式が残っていることの間を検査する。可能なら同じ実 source/receipt に対する二つの適合モデルを作り、元の B6 row と mode を固定したまま片方で固定先等式が不成立になることを示す。独立した現行の typed retention 経路が見つからなければ、R22 や public check の true を捏造せず、必要な typed retention 証拠を正確に記録する。

元の I65 statement / R21 / 既存 carrier・意味・spec は変更しない。全既存 witness の Bool も変えない。凍結ファイルの内容は読まない。
