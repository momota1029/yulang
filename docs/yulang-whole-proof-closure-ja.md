# Yulang 全体証明の主定理と現在の到達点

2026-10-24。全体目標は未完了である。本稿は、証明済みの核の定理を実際に合成し、元の全言語・推論定理に残る前提を明示する。表層構文や自然な推論を証明対象から除外しない。

## 1. 全体として示す命題

元の対象は、承認された Yulang の全 source constructor、宣言、名前解決、型・効果・profile、全称・存在証拠、一般化と使用、完全 Call、保護・解除、継続を含む。要求される主張を次のように分ける。

1. **意味論と宣言的健全性。** 各型付き source 導出から、その source の評価順・identity・保護・効果を持つ核の導出を構成する。実行は値型と効果契約を保ち、内部の型不整合で停止しない。
2. **推論の健全性。** 元の generation/accumulation/propagation/levels/extrusion/qualifying intrusion/generalization/use の成功結果から、上記の source 導出を構成する。
3. **元の推論能力。** 許された source の型付けを、元の lexical scope と共有資源を固定したまま表せる。要求された principal coverage・自然な推論・停止性を、その元の量化の下で示す。
4. **実装との対応。** 実 native constructor と消費側が、その算法と意味論を実現する。今回、実装の変更は対象外である。コードを書かないことから、この対応まで証明済みとはしない。

2 と 3 を、型付きの完成済み計画が与えられるという 1 の前提に置き換えてはならない。全入力の二値決定と、有限の証拠がある場合の成功完全性も異なる。

## 2. 合成する、独立査読済みの結果

以下の各稿の正確な前提を保持する。大きな旧原稿全体を査読済みと読み替えない。

| 記号 | 結果 | 今回の主定理での役割 |
| --- | --- | --- |
| G | [全制御経路 G1–G5](../notes/theory/2026-10-24-source-core-action-coverage.md) | 有限 source 導出から命令・body・七 frame を生成し、全実 step と失敗の吸収を被覆する。 |
| I | [有限 interface I1–I6](../notes/theory/2026-10-24-source-core-finite-interface.md) | 生成 graph に必要な観測欄と接続を構成する。実 identity・path・型 instance の全体を有限とは仮定しない。 |
| V | [値・継続 V1–V7](../notes/theory/2026-10-24-corrected-core-value-continuation.md) | 代入、primitive、capture、保存、進行、型付き反復再開、内部 code の導入契約を構成する。 |
| CM | [修正機械の simulation](../notes/theory/2026-10-24-corrected-machine-simulation.md) | 新規 witness、別 route、現在 world と保存 immutable data の再接続を含む。 |
| H | [handler 観測 H1–H5](../notes/theory/2026-10-24-correlated-handler-observation.md) | 同じ witness に関する相関を保持し、真偽両分岐・No・wait・再検索を被覆する。 |
| R | [共起 recipe S1–S6](../notes/theory/2026-10-24-cooccurrence-source-recipes.md) | 有限 signed signature graph から元成分別の recipe と実 receipt 表を作る。 |
| T | [任意代入 T1–T5](../notes/theory/2026-10-24-source-recipe-substitution.md) | 有限導出に由来を付けて任意型代入・AllE/template の経路と recipe を構成する。既存の動的証拠は固定する。 |
| SI | [文字列補間 SI1–SI6](../notes/theory/2026-10-24-string-interpolation-elaboration.md) | 子式・選択・role 証拠から全 structured parts の展開と型導出を構成する。 |

I と V、および G5 との合成の査読範囲・固定 hash は[記録](../tasks/agent-loop/sprints/core-interface-value-20261024-outcome.md)にある。R の有限 graph 前提は I によって自動的に除去されない。

T と SI の[査読記録](../tasks/agent-loop/sprints/source-substitution-surface-20261024-outcome.md)は、由来を保持する source 構成と、明記した局所証拠の下での文字列補間に限る。T の飽和性は正の出力位置についての主張である。

## 3. 修正候補核の値・効果・再開の統合定理

### 入力と検査条件

`d` を、G が扱う名前解決済み source/evidence の有限型導出とする。有限の宣言 body と再帰参照を含めてよく、実行の停止は仮定しない。recipe を必要とする箇所では R の構成入力、または別途正しく構成された具体 recipe を使う。候補核の source profile・permission 規則は各稿に固定したものとする。

`Gen(d)` を G1 の有限命令 graph、`B_d` を I の有限 cell universe、`F_d` を seeds と命令・code・cut 閉包の同時単調作用素とする。`U_d` は次を満たす有限証明書である。

```text
Seeds(d) ⊆ U_d
F_d(U_d) ⊆ U_d
各 immediate / latent / reentry 出力について U_d(out) ⊆ Φ_out
```

最後の包含は、同じ実 cursor・instance の契約解釈に対して検査する。別の path の許可を流用しない。`F_d(U_d) ⊆ U_d` は順序論でいう pre-fixed 条件である。証明書が存在することを、任意に小さい annotation の推論成功と同一視しない。

初期 graph・入力の型と精密契約が一致することを要求する。内部で作る lambda/delay/eabs/wrap/continuation の型契約は V で導く。真に外部から来る応答・code には、同じ operation instance の値型、既存 graph を変えない型付き拡張、宣言した精密効果契約を要求する。外部環境が必ず応答することは要求しない。

### 定理 C（有限 prefix の統合健全性）

上の入力と検査条件の下で、修正候補核の任意の有限実行 prefix に対して、次が成り立つ。

1. 現在計算・graph の値型が保存される。末尾は型付き Ret、同じ payload/response instance の Req、列挙した言語上の Fail、または次の step を持つ計算であり、型不整合による Bad にはならない。
2. 現在の観測と全 exposed event は、対応する `U_d` と `Φ_out` に含まれる。保護、実 crossing、現在の寿命関係、handler の許可を同じ joint evidence で解釈する。
3. 保存済みの継続へ同じ型の応答を何度与えても 1 と 2 が保たれる。過去の receiver/receipt/route を freshening せず、現在 world と再接続する。

**証明。** まず G1 により、各 body と直接結果 adapter を含む有限の命令表を構成する。I1–I6 により、この表の local/edge/frame interface と有限 domain を実際に構成する。非正則な型の実 instance は concrete descriptor に残り、現在読む equality・path query の実結果は対応 cell に入る。

V1–V4 は型付き graph の拡張、置換、各 primitive と実際に切り出す七 frame の型導出を与える。従って内部の closure と K の型安全性を外部仮定にせず、V5 の一段保存と V6 の進行を適用できる。これで G5 の value safety 前提が成立する。

実行 prefix 長へ帰納する。初期状態の cell は構成した seed に入り、`Seeds(d)⊆U_d` を使う。内部 step では G2 が実際の命令 edge を与える。I3 と CM により実 successor の cell がその edge の像に入り、`F_d(U_d)⊆U_d` で U 内に残る。同時に V5 が値型を保つ。

handler の選択では I4/H1 が具体 query と cell の真偽を一致させる。H の両 filter により、実際の許可・不許可のどちらも該当枝に含まれる。arm の正常 body result は実 adapter を通ってから Yes になる。その途中の request/failure は通常の bind/wait の edge であり、消去しない。No は保存時の query 結果を使わず、現在 world との Rejoin 後の edge へ進む。

capture/resume では G3 の実 frame word、I5 の有限 summary 閉包、V4 の型付き response hole を使う。保存した immutable data と現在 world の joint tuple は I3/CM の Rejoin に含まれる。外部 response は同じ Q 型と精密契約を持つため、V1 の代入と G5 の reentry 接続へ帰着する。保存 K は変わらず、各再開に同じ議論を適用できる。

Fail に入った後は G4 により七 frame が失敗を伝播するだけで、後続の query/No/Call は生じない。失敗 cell から正常経路へ戻る edge もない。ここで world を忘れることから具体 cleanup の規則は導かない。

以上で各 prefix の値型と cell 包含が得られる。出力について最後の mandatory inclusion を使えば Φ の上界を得る。V6 により stuck/Bad を除く。無限実行に最初の違反があれば、その有限 prefix の結論に反する。□

この定理は有限実行に長さの上限を置かず、計算の停止を結論しない。整数のゼロ除算など、列挙された言語上の Fail を型不整合と同一視しない。

## 4. 元の全体定理に残る、具体的な接続

| 義務 | 必要な証明 | 既に得た結果では不足する理由 |
| --- | --- | --- |
| 全表層の導出構成 | module/visibility、生成宣言、role/impl、act copy、error、各 sugar、rule、Yumark の全 source から意味を保つ d を構成する。 | 13式・11 pattern・3 statement の被覆は、全 frontend の導出構成そのものではない。静的 Yumark の内部は別稿で構成済み。 |
| 共起の生成と実表現 | T の任意代入・由来構成を compaction・再帰中心・既捕捉 descriptor の所有へ接続し、一般の class 生成を構成する。 | T は有限 path の exactness と parameterized recipe を与えるが、非正則な全位置言語の equality 算法を与えない。消去済みの表示から元 receipt の由来を復元したとはしない。 |
| source 観測との一致 | 修正候補の owner/permission/寿命規則が、承認済みの source の観測を満たすことを示す。 | 値保存はどの全域 eligibility でも成り立ちうる。意図した handler が捕捉することは別の主張である。 |
| 元の Simple-sub A/B | 各実 extrusion の qualifying parent/copy 等置を、元の source scope・共同 witness・publication/use を保って持ち上げる。 | 点ごとの diagonal extension は、一般化された複数 use における共同 strategy を構成しない。 |
| 局所存在 evidence | head skolem と non-generic 資源を固定し、mixed-variance/recursive な局所存在座標を非総当たりで構成する。 | 完成した certificate の検査や lower union の選択だけでは witness の発見を証明しない。 |

元の A/B の量化と最初の欠落は[侵入の source 保存稿](../notes/theory/2026-10-13-intrusion-source-preservation-proof.md) §1・§3・§5、局所存在構成は[拡張稿](yulang-whole-language-semantics-ja-expanded-20261023.tex) `remaining-conformance` に保持する。強い全モデル一致を追加したり、source を縮小したりして元の義務を置き換えない。

### 4.1 再帰と局所一般化について実際に試みた接続

次の同じ source を、候補核と元の member/world 意味論の両側から構成した。

```text
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

[候補核の具体的導出](../notes/theory/2026-10-24-correlated-helper-core-derivation.md)では、U=Int∨Bool、V={a:Int,b:Bool} として、同じ一つの f:C(U,V) を捕捉する `g:∀A.(A⇒U)⇒C(A,A)` を構成した。Int と Bool の二使用、捨てられる f y の結果、wrapper の完全 Call と pending suffix を全て保持する。

[元の member/world 構成試行](../notes/theory/2026-10-24-correlated-helper-original-member.md)は、この具体的な構成を元の theorem へ移す際に、次の二 judgment が未導出であることを示す。

- **J_rec:** この body を持つ実際の f と同じ world を、元の独立した formation/registry/profile/CompleteMem/KV 条件を満たして同時に導入する。既に採用された再帰導入は `f x=g; g y=f` の厳密な場合に限られる。一般の body の安全性から独立 guard の成立を結論する規則はまだ構成されていない。
- **J_pub:** 構成中の同じ f を g が捕捉するとき、その完全な依存を元の Source-Generalize の walk に渡し、f と world を共有したまま g の二つの正当な使用を得る。表示された f の型に A がないことだけでは、全 capture/admission/future evidence に A がないとは言えない。

これは元の source が不正だという判定でも、intrusion の反例でもない。元の形成条件への bridge が未構成なので、候補核の導出と既知の native scalar failure を組み合わせただけでは、そのどちらも結論できない。正当な未定義部分の定義は引き続き許されるが、既に固定された独立述語を都合よく真へ置換することは証明にならない。

`'e?` の別意味論や入力選択は、この表に未決事項として復活させない。[直接訂正](../notes/design/2026-10-24-cooccurrence-release-clarification.md)に従い、保護の動作原理と同じ共変位置への共起から集約を説明する。残るのは、その対応を元の全生成・代入へ適用する証明である。

## 5. 完了の判定

定理 C の成立により、生成済み核についての「有限 interface が適切」「内部 continuation が安全」という未構成の仮定は除かれた。次の作業は §4 の各 source/算法接続を構成し、1節の元の主張へ戻すことである。現段階で全言語・推論の証明が完了したとは報告しない。
