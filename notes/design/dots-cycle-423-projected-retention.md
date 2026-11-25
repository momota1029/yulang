# C423 C14: 元の projection と固定出力先の保持を分ける

先行 C422 の `SourceHead` / literal `HeadMeaning` の反例と、同じモデルの projection/元 B6 の値側は使い直す。旧の結論・分類・入口は変えない。

- この周は、元の authored record 両端点による `Read` と元 B6 の出力を得た後、ordinary State に**すでにある**固定先の等式を、真の projected RHS と同じモデルで結ぶ。出力先・元の出現・宣言番号・out番号を書き換えない。
- 狭いが真に非点の形: 中心 record 行は読まず、元の上下端点の field も別に保つ。独立に根拠づけられた二つの補助 record が同じ field 名をもつとき、その補助の lower ≤ 実中心 ≤ upper が既存の普通制約にあることを照合する。補助の endpoints は実中心と別名。前段の候補照合は元の endpoints のまま。
- 今の ordinary の `target = variable(field)` を実 row ordinal で検査する。2 方向の projection を使って、任意の適合モデルで **本当の actual RHS** と target が同値であることを証明。既存の型値を検査するのであり、新しい literal center・fresh 名・新しい仕様上の拒否を作らない。
- テストでは元の field 範囲を `int ≤ (int|bool)|str`、補助が選ぶ実 field を `int|bool`、残余に幅を残す。元の中心も元の上下端点と意味上非同値のモデルを使い、中心 record 行がないまま、保持の式と旧選択の証拠を分けて検証する。
- 出力保持が閉じても fixed `Event.head` を捏造せず、C14 の closure は R/check/sound のすべてが揃わない限り数えない。I-74 の他行は触らない。
