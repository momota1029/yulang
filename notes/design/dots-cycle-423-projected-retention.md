# C423 C14: 元の projection と固定出力先の保持を分ける

先行 C422 の `SourceHead` / literal `HeadMeaning` の反例と、同じモデルの projection/元 B6 の値側は使い直す。旧の結論・分類・入口は変えない。

- この周は、元の authored record 両端点による `Read` と元 B6 の出力を得た後、ordinary State に**すでにある**固定先の等式を、真の projected RHS と同じモデルで結ぶ。出力先・元の出現・宣言番号・out番号を書き換えない。
- 狭いが真に非点の形: 中心 record 行は読まず、元の上下端点の field も別に保つ。独立に根拠づけられた二つの補助 record が同じ field 名をもつとき、その補助の lower ≤ 実中心 ≤ upper が既存の普通制約にあることを照合する。補助の endpoints は実中心と別名。前段の候補照合は元の endpoints のまま。
- 今の ordinary の `target = variable(field)` を実 row ordinal で検査する。2 方向の projection を使って、任意の適合モデルで **本当の actual RHS** と target が同値であることを証明。既存の型値を検査するのであり、新しい literal center・fresh 名・新しい仕様上の拒否を作らない。
- テストでは元の field 範囲を `int ≤ (int|bool)|str`、補助が選ぶ実 field を `int|bool`、残余に幅を残す。元の中心も元の上下端点と意味上非同値のモデルを使い、中心 record 行がないまま、保持の式と旧選択の証拠を分けて検証する。
- 出力保持が閉じても fixed `Event.head` を捏造せず、C14 の closure は R/check/sound のすべてが揃わない限り数えない。I-74 の他行は触らない。

## 実装と最も重要な追加対照

- 元の ordinary row に固定先 `12 = variable 7` と、実中心名 1 の上下にそれぞれ record 補助端点 8, 9 がある例を検証。元の照合端点 0, 2 の field 名は 3, 4、実 field 7 は `int|bool` でどちらの端点型とも非同値。尾部が異なる二つの同じ State の適合モデルで、元の B6 本体はどちらも同じ固定先 12 のこの field を返す。中心の literal 行は含めない。
- さらに 7, 10, 11 が別の論理名でも、保持されている `12 = 11` と実向きの普通制約 `11 ≤ 7`, `10 ≤ 11` から同じ結論。片方を外すと同じ元 B6 値が得られる一方、固定先を上または下にずらせる具体的モデルがそれぞれ存在。型エラー判定ではない。両方向の条件が実際に検査する意味を持つ。
- 上下の root/field 証拠は各位置で raw 間隔行と `tyLe(var,var)` を順番に照合する有限の道でも構成できる。向きや row ordinal をすり替えない。
- **required/optional の一致自体は必須ではない。** 実中心 1 を `(record x field exactEmpty) ∩ exactEmpty` と `record x field exactEmpty` の二つの既存 ordinary bound で挟む別の断片では、required 射影だけを同じ固定先に結べる。実例は両 channel が非同値の適合モデルで、元の B6 RHS と保持値は一致する。古い literal record の再構築や希望した optional 同値を言い換えていない。
- 四つの実 data wire を受ける `readRetainedPickWrite423` は、同じ元 endpoints → 元 associated lookup/B6 → exact retained row の準備用読取り。実際の model/value/verdict を証人に埋め込まない。exact row 座標・全捕捉区間・同じモデルでの値側と固定先の同値を出す。元の `check` はこれを勝手に成功分岐へ変えない。

C14 の残りは、この元出現の source projection を受け取れる head 証拠と、それを使う完成した分類・公開入口・健全性。現在の固定 interface を変えずに、投影済みの出力があることだけから欠けた head は得られない。新しい言語判断は導入しない。
