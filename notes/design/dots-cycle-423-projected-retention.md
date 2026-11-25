# C423 C14: 元の projection と固定出力先の保持を分ける

先行 C422 の `SourceHead` / literal `HeadMeaning` の反例と、同じモデルの projection/元 B6 の値側は使い直す。この周の公開差分では旧の結論・分類・入口を変えない。後記 I-75 が次の追加構成子を許可した。

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

## 途中で I-75 に切替

`integration/m1-final@b2fe5a3d9324aa1ef2964c95f7445884ee4dd66e`、Inbox `42ed184178357af37ba86de355218d720cb36746`。I-75 は roles §6.5 に合わせ、I-65 の外側の定理文を保ったまま、端点の場合の source と意味の構成子を足すことを認めた。この周の公開差分は旧構成子・分類・入口をまだ変えていない。

- `source_endpoints_have_projected_meaning423`: 上下それぞれの元 syntax と既存の ordinary row、および元の要求区間から、任意の適合モデルで required と optional が別々に元の field 区間内にあり、mask が残余区間内にあると証明。実中心を literal record と仮定せず、元の名前も変えない。この独立モジュールは C365/C336 に依存し、C422 や checker に逆依存しない。
- `checked_preparation_supplies_I75_head_and_actual_target423`: 実際の準備入口による元 endpoints と compiled B6 output から上の証拠を得て、同じモデルで実 field 射影を元の固定先と結ぶ。required/optional が非同値の fitting model でも元の出現 `[61,423]`、宣言 1、出力 0、固定先 12 を変えない。射影を既存の alias 名に書き換える主張ではない。
- 正本 `GeneralDeclarativeI65Heads367.lean` blob `86a2e8b39f8933f64c1b0963af7d91656ce5196c` の隔離試作では、`SourceHead.endpointRecord` と対応する `HeadModel.endpointRecord` を追加し、`source_head_sound` の旧 ordered/joined 分岐を維持した。実 `PreparedWrite` から新構成子を作り、そのモデルで意味を示すところまで Lean 4.35.0 strict で通った。全依存を再検証した正本の変更ではないので、試作自体は公開コードに含まない。

### 次の接続順

1. 上の新構成子を、元 request の singleton、宣言の literal record field/tail、別々の binder、および `Inputs` で索引する。旧枝の比較は維持。ただし C422 の「旧 `SourceHead` のすべてを反転する」否定を新構成子まで量化してはならない。旧 ordered/joined のみに限定する述語と、既存 R0–R13 がその旧枝だけを使うことを検証し直す。literal 同値そのものの反例は消えない。
2. C402 の `Event.outputs` / `LocalRhsMeaning` / `FixedTargets` と C408 の `encodedEventWrites` を併せて確認する。現 `NamedMixedReceipt401.actualEquation` は `AuthoredBodyFrame393.slots` の名前三つ組の center を読む。元 record center を field slot と読み替えてはならない。既存の ordinary target とその変数が射影と同値であることは、元の B6 binder の正しい評価をそのまま記録することとは別。旧 named branch を残したまま、同じ元 B6 plan/body/index と projection の位置を運ぶ必要がある。この周では公共 wire を作らない。
3. 候補・raw root K2・元宣言と出現を変えずに R14 を作り、同じ固定出力の witness-only 公開分岐と同じ形の dictionary/check sound の両方を通す。旧 42+13 対照は変更後の実公開入口でも再実行する。I-75 の変更を別の言語診断やチェック全体の完全性とは数えない。
