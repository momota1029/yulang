# C408: check / check_sound の境界

仕様の受理範囲ではなく、1 本の Bool 検査器の受け取れる証人の範囲を記録する。R₀ 自体は C407 のまま。C407 の [R₀ 対 spec の一覧](dots-cycle-407-i73-coverage-list.md) は変更しない。

| check の入口 | 実際に確認すること |
|---|---|
| rawRoot | C350 の元 Wire の引数・ノード・alias 閉路を同じ ordinary State/元 demand で検査。報告は同じ rejected tree/verdict、実書込みなし。release も候補の推測も不要。 |
| nullary | 同じ Problem の全可視一覧がちょうど一つ。名前・arity・宣言範囲が同じ metadata 検査を通り、空の引数・head・where・要求出力から C403 の実 Event を作る。その ID の葉、同じ辞書、実書込みなし。 |
| unsupported | false。言語上の pending/rejected の根拠は作らない。 |

R₀ が既に表すが今回 check が受け取らない例: 非空の変数引数（元 OriginRoute と Bounds が必要）、反復変数の選択後の中心 tie、順序付き where、associated output の実書込み、同じ型付き authored native、実到達子 K2、複数候補の ambiguous。古い checker の証人をこれらに使う際には、同じ Problem の元の要求・元宣言・出現・固定先・B6 型木・出力順に照合する。「古い checker が true」は代わりにならない。

`ClassifiedAs` は同じ報告木の実 `SourceTrace R0`、その元 summary、元の Event の書込みの親/where 順を要求する。型木を保持した `traceWrites` と旧 C402 canonical ledger が一致することも証明。非空の出力木を型の近似で比較する実行判定は追加していない。

`ReportEvidence` は同じ木で、各選択ノードの head/typed RHS/固定先を同じモデルで示し、成功する子辞書も同じ順で証明する。選択を支えた producer は追加の診断子や出力として重ねない。

この段階はモデル・proof を外からもらう checker ではない。範囲拡大は、2 と 3 の統合確認後に C の項目として扱う。