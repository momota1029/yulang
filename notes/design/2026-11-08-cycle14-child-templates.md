# Cycle14: structural child templates (Draft)

2026-11-08. I-7 generated_work_closed の部分。意味論は追加しない。

データ: cycle13 の Endpoint n、source slots は Fin n のまま。`extract depth` は構造的 capture を source endpoint から取り出す。固定 Ty の部分木は fixed、slot そのものは同じ slot。`plug` は where Template の変数へ Endpoint を代入する。
独立判断: 既存 Inspect / production の実 capture 位置（cycle11）。
実行版: extract と plug、requirement から子 SourceRequest を作る。
定理の型: 任意の n, depth, endpoint e, State s について、extract の結果を eval した Option と atDepth depth (eval s e) が等しい。任意の Template t, Endpoint e, State s について eval s (plug t e) = instantiate t (eval s e)。任意の実 production と head capture position から lower/upper の source Endpoint が得られ、それらで作った全 where child の evaluation が実 children と一致する。

これは動的 child に source slot を残す橋。任意の後続状態で同じ宣言が再選択されるとは主張しない。一般 interval、source graph allocator、飽和、B4 の完成ではない。5つの主要橋は依然残る。Yulang2 x-oracle の X13–X16 を参照したが新たな実機照合ではない。

## 構造的停止の橋への拡張

`shape` は source slot を unknown とした静的形。eval 後の Form は任意の状態でこの形と等しい。`sourceWeight` は lower/upper の形の Paterson weight 和。
`Generated registry child parent` は、任意の状態での実 production、capture の source extract、実 where requirement を証拠に持つ関係。状態は辺ごとに異なってよい。検査済み registry について、全 child,parent と Generated の辺で sourceWeight child < sourceWeight parent を導き、任意の parent の Acc を導く。外部の Acc/fuel/finite closure は仮定しない。
ただし `production` は scan の最初の hit であり、unique selection ではない。飽和の同親再訪はこの relation に含めない。有限な子領域の列挙、一般 interval adapter、source graph allocator は未完成。
