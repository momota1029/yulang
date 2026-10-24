# Yulang 全体証明の主定理と現在の到達点

2026-10-24。全体目標は未完了である。本稿は、証明済みの核の定理を実際に合成し、元の全言語・推論定理に残る前提を明示する。表層構文や自然な推論を証明対象から除外しない。

**最新の intrusion 規則:** [生成レベル別 SCC の直接決定](../notes/design/2026-10-24-birth-level-scc-intrusion.md)により、固定された Value 生成レベルごとの誘導グラフで資格を判定する。§4.1–§4.4 の跨レベル F/G 等置・native failure は旧規則についての履歴であり、現行算法の拒否として使用しない。現行の適用は §4.5 に示す。

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

元の A/B の量化と最初の欠落は[侵入の source 保存稿](../notes/theory/2026-10-13-intrusion-source-preservation-proof.md) §1・§3・§5、局所存在構成は[拡張稿](yulang-whole-language-semantics-ja-expanded-20261023.tex) `remaining-conformance` に保持する。強い全モデル一致を追加したり、source を縮小したりして元の義務を置き換えない。extrusion/intrusion の後続証明は §4.2 にまとめる。

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

これは前回の構成試行の境界であり、後続の §4.2 は actual registry/capture の構成を進めている。元の source が不正だという判定でも、intrusion の反例でもない。元の形成条件への bridge が未構成なので、候補核の導出と既知の native scalar failure を組み合わせただけでは、そのどちらも結論できない。正当な未定義部分の定義は引き続き許されるが、既に固定された独立述語を都合よく真へ置換することは証明にならない。

`'e?` の別意味論や入力選択は、この表に未決事項として復活させない。[直接訂正](../notes/design/2026-10-24-cooccurrence-release-clarification.md)に従い、保護の動作原理と同じ共変位置への共起から集約を説明する。残るのは、その対応を元の全生成・代入へ適用する証明である。

### 4.2 extrusion / intrusion と SCC の後続証明

[Value SCC と等置の証明](../notes/theory/2026-10-24-value-scc-qualification-proof.md)は次を構成する。

- source 所属 Name からの辺と helper graph の到達可能性保存。元の値の SCC は型の bounds から作らない。
- SCC 分割、辺 A→B の追加で合併する正確な集合 `Reach(B)∩Pred(A)`、初回成功・凍結条件の下での native SCC 計算。
- 実 extrusion occurrence の origin/receiver と polar parent/copy pair による資格判定、有限固定集合での activation/equality 処理の終了。
- finite-store native extrusion 一回の終了・level 上界。極性 memo により、高 level の元変数が h 個なら copy は最大2h個。
- 全旧制約を保持する型 quotient の意味保存と、既存 extrusion 定理を通じた元の局所 demand への健全な含意。

旧規則の具体例では definition-root の F→G と G→F から実 pair C=B,D=R の資格を導いた。現在は birth(F)≠birth(G) のため、この適用を置換する。一般グラフ補題と局所 extrusion の結果は各生成レベルのグラフに再使用できる。全 source の fragment membership、contextual occurrence transport、全 caller lifecycle と combined inference の停止を、この局所証明から自動的に結論しない。

[recursive formation の後続構成](../notes/theory/2026-10-24-original-recursive-formation-construction.md)は、finite declaration registry、同じ r_f を共有する f/g/wrapper の実捕捉、全 pending plan、active capture の参照 record を構成した。選択済み native signature grammar と unannotated policy を適用し、既存の pair/step case と同じ raw graph に戻ることも示す。

この段階で残った接続は、(1) active r_f に対する q_fy の完全 Call/operator law と whole-carrier admission action、(2) 構成した ActiveCapture record の全 typed field を元の Generalize walk に対応付ける証明である。§4.3 は (1) の入力 action を構成する。条件付き postfixed assembly は完全な member/world witness とは区別する。

両稿の固定版、査読範囲と残項は[今回の記録](../tasks/agent-loop/sprints/extrusion-intrusion-scc-20261024-outcome.md)にまとめる。元の lawful-use coverage と主型性は引き続き OPEN である。

### 4.3 完全 carrier の入力構成と閉包判定

[Call/admission の構成](../notes/theory/2026-10-24-original-call-admission-construction.md)は、同じ full carrier policy に対して `I_A=I_U∧Ret_A` を作り、元の carrier・world・receipt・pending・response・future を保つ射影を構成した（CA1）。actual current world と hereditary y:A の下で、同じ NameDelay の全 Force/prefix/future 証拠も構成する（CA2）。今回の未注釈 witness の I_U を既存の full `Comp(empty,U)` に選ぶと、NameDelay から I_U への checking は恒等になる。この選択は、独立に固定された別の inlet を上書きせず、admitted carrier を source の NameDelay だけに制限しない。

これを recursive assembly に戻しても、J_rec 全体はまだ出ない。候補集合 S に f が属するという事実から、完成済み membership `νΦ` の elimination を使うことはできない。実 f/g/wrapper の全 phase に対する `S.V⊆Φ_V(S)`、`S.W⊆Φ_W(S)`、`S.T⊆Φ_T(S)`、`S.Car⊆Φ_Car(S)` の同時導出が残る。CA2 が用いる actual world/value の前提も、この適用時に候補集合の要素で置き換えてはならない。

[ActiveCapture の閉包判定](../notes/theory/2026-10-24-active-capture-generalization-closure.md)は、元の Generalize walk を各 field に適用し、最後に不足する complete typed field graph/action を特定した。完全な graph N があれば、A が retained な own Desc で `A∉Fix_N(p_g)` であることが template eligibility の条件になる（WA1）。同じ r_f と FullRelation の参照、表示された F:U→V の自由変数だけでは、この条件は導けない（WA2）。実 source の graph に対するこの判定と action は未完である。

独立査読は CA1/CA2、今回の inlet 選択、WA1/WA2 の明記した範囲を受理した。[固定版と査読記録](../tasks/agent-loop/sprints/original-call-active-walk-20261024-outcome.md)に残項を保持する。whole production C0 を主張する箇所では、実際の nonstructural clauses の元の証拠も必要であるが、これを孤立した NameDelay 入力補題の追加前提にはしない。J_rec/J_pub、元の source-qualified 反例、全体証明の閉鎖はいずれも得ていない。

### 4.4 Raw execution からの再構成と固定二 view

[raw-observation 稿](../notes/theory/2026-10-24-original-raw-observation-postfixedness.md)は、有限 raw 導出の反転・帰納から、wrapper/g が正常に返る場合の同じ y との相関、record の field provenance、全未完了 suffix を構成した。一つの実 allocation/history 族 S を使い、完成済み membership を再帰的に仮定しない。exact value holes H を source-created g/wrapper まで含む族に拡張した relative lift と、candidate-relative carrier projection/NameDelay も構成した。

この方法でも、raw observation を S.T に入れただけでは、その observation が元の full `P_F*[S]` の全独立 conjunct を満たすことにはならない。source phase から全 envelope への map（RP-FULL）に加え、各 closure の formation/profile、source world の joint guard、carrier/retained-field の全 case が残る。査読で q_fy 一件への残項集約に MAJOR 指摘があり、この全 family を保持するよう修正した。record formation は latent fields を force しないため、f の非停止を無条件に使う方法も採用しない。

[固定二 view の source 合成](../notes/theory/2026-10-24-active-capture-field-graph.md)は、g の actual Parameter/inlet を U に固定したまま、同じ g の G_Int/G_Bool の完成した証拠を intersection にまとめ、一回の Bind と二つの monomorphic Name/射影で使う構成を与える。これにより、この別の source 証明では polymorphic J_pub を前提にする必要がない。ただし二つの complete memberships 自体に上記の全 family の導出が必要であり、現時点では条件付きである。

[今回の査読記録](../tasks/agent-loop/sprints/original-raw-postfixed-20261024-outcome.md)は、受理された限定補題と、MAJOR 指摘により撤回した全四 sort の十分性を区別する。修正は不足する証明を追加したものではない。

同稿 FG3 は、旧 intrusion の native shared-C failure と明示的受理契約が両立しないという条件付き結果である。後の生成レベル別 SCC の選択により、その failure を生む等置の資格が変わった。この旧拒否を維持するかという受理意図の質問を現在の待ち条件にはしない。未回答を肯定・否定に読み替えず、新規則の履歴を §4.5 で直接扱う。元の CompleteMem witness と全体命題が証明済みになったとはしない。

### 4.5 生成レベル別 SCC への変更

[新しい資格規則](../notes/design/2026-10-24-birth-level-scc-intrusion.md)は `V_k={v | birth(v)=k}`、`G_k=G[V_k]` とし、実 occurrence の origin と receiver が同じ G_k の SCC に属するときだけ、その parent/copy pairs を intrusion する。birth は Value 生成時の固定ラベルであり、型座標の現在 level と区別する。cross-level の元参照は保持する。

[後続証明](../notes/theory/2026-10-24-birth-level-scc-intrusion.md)は、この資格と各 level 内の相互到達性、SCC 更新、有限固定集合での処理を扱い、旧局所 extrusion/diagonal lift を元の demand 前提の下で適用する。nested F/G と O/E は異なる birth のため、その跨レベル occurrence は親子等置を追加しない。先ほどの helper の拒否導出を、現行規則の反例として残さない。

同一 cut の局所 lift と、source の一般化・捕捉・複数使用を通じた joint strategy は区別する。現在の必要な証明は、**新資格を持つ**各 occurrence の source-scoped lift と、その全 consumer への対応である。旧跨レベル資格を証明することを、この新算法の前提にはしない。正確な成果・査読範囲は[今回の記録](../tasks/agent-loop/sprints/birth-level-scc-20261024-outcome.md)にある。

### 4.6 同じ生成レベルの再帰から生じる低いコピー

[具体的 replay の導出](../notes/theory/2026-10-24-birth-level-replay-intrusion.md)は、自己再帰 f の結果を外側の h に渡す source を固定する。元 Simple-sub の全 scalar bounds を辿ると、f の完成時に `Record(B₂) <: C₁` が replay され、実際の親子 pair `(T₁,B₂)` が生成される。F/F は新資格を持つが、この後続コピーの occurrence が F/F に属するかは別途導出を要する。

実 contextual code について証明した BR1 は、replay が依存元の source set の和集合を保持するという命題である。対応する投影経路が実 source から生成されれば F/F と F/H の両 seed がコピー生成まで伝わる。これは各 seed がそのコピーの actual occurrence を所有することの証明ではない。現在の `any` consumer による等置と、採用された意味論への正当な対応を区別する。

[公開後の二使用の導出](../notes/theory/2026-10-24-birth-level-publication-replay.md)は、B₂ を使用ごとに複写し T₁ を共有する正確な freshening map と Int/Bool の二使用を構成する。もし公開前に B₂=T₁ を等置すれば、二使用は一つの固定 anchor を共有し Bool<:Int を要求する。この含意は証明できるが、実 source の完全な producer path、コピー・再利用 occurrence の所属 BR-ATTR、等置の消費時点は未証明である。

従って今回の結果を新規則の反証や全体証明の完了とはしない。BL-JOINT の次の接続は、この実 pair に対する source 所属と公開作用である。固定版・独立査読・残る元の義務は [replay sprint 記録](../tasks/agent-loop/sprints/birth-level-replay-20261024-outcome.md) に記す。

### 4.7 保持したグラフを取り出して判定する

ユーザーの指摘に従い、[実 graph の隣接表と SCC](../notes/theory/2026-10-24-retained-value-graph-replay-attribution.md)を取り出した。前例の F、H、wrapper Lambda は別頂点であり、成分はいずれも singleton である。F→F はあるが、F→H や F→X の先から F に戻る経路はない。従って F/F は資格あり、F/H と F/wrapper は資格なしと計算できる。

コピーの記録だけでなく、物理的な B≤T リンクの作成記録、実 processing relation、順序を保持した Replay.upper_input、元の R≤C extrusion-link を辿ると、h-call の F/H association まで戻れる。lower 側の自己呼出し F/F の経路も別に保持されている。「source set を混ぜたので graph が失われた」という説明は当たらない。

[公開への適用](../notes/theory/2026-10-24-retained-graph-publication-consequence.md)は、全 graph・実 association・pair list を持てば SCC 判定が有限計算で一意に決まることを示す。現 `any` consumer の query は F/F を拾うため真、実 upper boundary への遡及 query は F/H なので偽となる。残る source/native 証明は、採用規則の receiving occurrence をその実経路から導くことである。SCC の選び方を新たにユーザーへ求める問題ではない。

抽出時には現 graph builder の FieldTail owner walk の漏れと、immutable birth の未保持も特定した。数学的 source graph とこの実装差分を分けて記録し、実装は変更していない。[査読記録](../tasks/agent-loop/sprints/retained-graph-replay-20261024-outcome.md)に具体的範囲と残項を示す。

### 4.8 遅延した extrusion と有限使用の解対応

[完全 Call の receiving incidence](../notes/theory/2026-10-24-replay-receiving-occurrence-proof.md)は、内側 f の origin と外側 h の argument placement を同時に保持する RP1 を構成する。これは authentic inputs と typed field maps を入力とする source の結果であり、新たな solver copy の所属までを含まない。RP2 は列挙した構造公理に限り、保持済み source/Call/replay データを同じにした二つの association 解釈を与える。全言語意味論の独立性や source 保存の不可能性は主張しない。

[制約の可換性と公開後の解の引戻し](../notes/theory/2026-10-24-replay-extrusion-commutation.md)は、先に下界を展開する場合と後の replay で展開する場合の具体的な native store の同型 EC1 を証明する。実 extrusion group は一つと二つなので、この同型は occurrence の同型へ自動的に拡張しない（EC2）。

さらに、この実 store の B=T 等置について、任意有限回の freshening と quotient を結ぶ写像 q_m を構成した（EC3）。等置後の graph と任意有限 client 制約の解を q_m で引き戻せば、等置前の同じ公開 root と client の解になる（EC4）。この具体的な有限 native 使用で解を増やさない方向は閉じた。任意の solver 実行順や追加一般化、全 source context を量化した結果ではない。逆向きは既存の Int/Bool 二使用で成立しない。

RG-OWNER、全 source の原 A/B と安全性は残る。SCC と境界 query は構成済みだが、実 delayed copy と source receiving occurrence を結ぶ式は今回も証明できていない。[査読・到達点](../tasks/agent-loop/sprints/replay-receiver-proof-20261024-outcome.md)を参照。

### 4.9 同 birth の引数 replay と両極性の境界

[同生成レベル Call の native 構成](../notes/theory/2026-10-24-birth-level-extrusion-redundancy.md)により、「同 birth の呼出しなら、全派生比較で extrusion が不要」という候補不変条件は反証された。先行する `h x` が B₂≤C₁ を作り、後続の自己呼出し `f {a=y}` と f completion の反変引数から Record(Y₂)≤C₁ が生成され、実 T₁/Y₂ copy が生じる。これは生成レベル別 SCC の intrusion 意味論の反例ではない。

[残余要求の構成](../notes/theory/2026-10-24-residual-demand-source-association.md)は、正境界 a≤c では後着下界 d を b∘d、負境界 c≤a では後着上界 d を d∘b として運ぶ native replay を証明する。Function の引数では比較方向が反転するので、常に upper を選ぶ規則へ一般化しない。source の完全な typed interface map が与えられる場合の合成も構成するが、それを native cut と対応させる元の source-to-constraint 生成は依然として証明対象である。

実装に保持される ScopedDemand.original_call は whole-Function demand の replay には残るが、Value extrusion link では default に、Function port 消費では None になる。この field を読むだけで delayed copy の receiver を決定する方法は使えない。保持された Derived/Replay/creation の経路と source typed map を接続する義務は残る。結果と査読範囲は[記録](../tasks/agent-loop/sprints/birth-residual-closure-20261024-outcome.md)に分ける。

### 4.10 source-indexed 生成と publication の一般不変条件

[Application と constraint 導出](../notes/theory/2026-10-24-source-indexed-constraint-derivation.md)は、元の実 Application emission から operand origins を作り、有限 native history に source の義務を付けて同時生成する。発行された義務と、それを満たす semantic evidence を区別する。既存の同じ x/world について NameDelay の inlet checking は得られるが、後着 Record に x の actual value/root を置き換える SC4 は、semantic world/history action が未証明と査読され撤回した。actual ValueBind/rebind からの構成、全 invocation の `CIncl`/`TypedCallCert`、再帰 f の membership、一般 history の whole-interface matching は残る。

[bound のレベル閉包と公開](../notes/theory/2026-10-24-native-level-closure-and-publication.md)は、元 native の全 finite ordinary history で、各保存 bound の level が所属行の level 以下であることを実 write site ごとに証明する（NL1–NL3）。従って低い shared anchor の下に高い依存はなく、実 freshenAbove がコピーする集合を正確に構成できる（NL4）。これは前の具体例だけの条件を一般化した結果である。

等置後は、全 clause を保持する quotient が同じ level 条件を満たすか有限に検査できる（NL5）。この条件と公開部分の class 飽和性の下で、任意有限個の使用との clause 対応、全域 valuation の pullback を構成し、既存 EC3 の実 store に適用する（NL6–NL7）。最小 level の選択だけでは条件は自動成立しない。元の source-scoped joint strategy と逆向き coverage、全 qualifying occurrence への適用、combined termination は未完のまま保持する。独立査読の受理範囲、source 側 SC4 の撤回と固定 hash は [outcome](../tasks/agent-loop/sprints/source-indexed-derivation-20261024-outcome.md) に記録する。

### 4.11 actual ValueBind と copy 履歴の有限導出

[actual Return からの Call](../notes/theory/2026-10-24-fresh-valuebind-complete-call.md)は、元の typed Return と実 entry/rebind から新しい dynamic binding を構成し、旧 root/value/history を保存する VB1 を導く。同じ h と同じ NameDelay に R/E を適用し、actual admission と receiver の全 prefix/pending/future を構成した。元の unannotated result endpoint は、H* が既に持つ **complete invocation Comp port** へ coherent に解ける場合、各 phase の証拠から CIncl を得る。任意の独立関係 P_H* の source Comp 表示、generated profile の対応、再帰 f の actual membership/history はこの結果から自動的には出ない。SC4 の旧 binding 置換は復活させない。

[copy 系譜による履歴の消去](../notes/theory/2026-10-24-copy-genealogy-history-erasure.md)は、fresh use をまたがない区間の各 copy を実 parent の base へ写し、初期 bounds と外側の source seeds だけから有限 comparison closure を構成する。実 replay・構造分解・両 polarity の extrusion・parent/copy quotient が発行する全 comparison の像をこの closure から導く（GE1–GE4）。その closure に failure がなければ実区間にも比較 failure はない（GE5）。一つの closure model は全 cut の diagonal lift を同時に与える（GE6）。原 native cache との完全同値や source semantic inversion は主張しない。

このため、局所 lift の各 cut に独立に置かれていた demand premise は有限 closure からの導出へ置き換わる。一方、元 source からその joint model/strategy を得ること、publication における独立使用、receiving occurrence、combined termination は同じ親義務として残る。固定版・独立査読範囲は [Call/history outcome](../tasks/agent-loop/sprints/call-realization-history-20261024-outcome.md) に記録する。

### 4.12 選択済み ReadInvoke の実適用と捕捉 Record 閉包

[generated Call の局所導出](../notes/theory/2026-10-24-generated-call-descriptor-typing.md)は、既に authoritative な [pure-read result constructor](../notes/design/2026-10-08-pure-read-call-result-constructor.md) を原 `h x` へ適用する。この immutable Name route では元の result が `ReadInvoke(H*,D_h,IF_h)` なので、HC1/HC2 の全 phase 証拠を定義の各 case に入れ、HC-RESULT を閉じる。任意の抽象 P を別の Comp grammar へ表示できることは、この選択済み case の前提ではなかった。GC1/GC2 は実 field injections と由来の分割、GC3/GC4 は元 operand judgments と独立 arm-local laws からの局所 typing 関数を構成する。全 TypedCallCert の未列挙 field、actual local profile/permission formation、未供給の独立 arm laws は残す。

[捕捉した x を返す Record wrapper](../notes/theory/2026-10-24-captured-record-wrapper-introduction.md)は、元の `lambda z.{a=x}` に selected Strict constructor と source Record rule を適用する。actual x の hereditary certificate から、creation-time capture、実 entry Return 後の fresh z binding、同じ x の field、全 pending/future を持つ complete wrapper と world の同時導入を構成する。元 primitive/history/alternative の独立契約を保持し、未使用 z の Value-entry を省略しない。これは原 result-replay source に必要な closure supplier であり、recursive f やその argument carrier の成立までは含まない。[固定版と査読範囲](../tasks/agent-loop/sprints/generated-call-operator-20261024-outcome.md)を参照。

### 4.13 原 monomorphic 再帰 instance と native profile

[Name Call を持つ再帰閉包](../notes/theory/2026-10-24-name-call-recursive-closure-membership.md)は、元の `f=λx.λy.{first=h x,next=f {a=y}}` について、A=Record(a:Int)、y:Int、genuine H* と元の独立 kernel/formation inputs の下で、同じ一つの f と全 actual inner closure family の V/W/T/Car を同時に構成する。f の entry 後の実 Lambda/Return から receiver の一段証拠を作り、未完成の candidate f に R/E を適用する循環を避ける。内側 body の h Call、再帰 f Call、Record の順序と実結果を保持し、NR1/NR2 を元の actual Return/rebind と HC-REC/HISTORY に適用する。全 polymorphic source instances、publication や native receiving 対応の定理へは拡張していない。

[native local profile 構成](../notes/theory/2026-10-24-native-local-profile-construction.md)は、この source の actual licensed projections に対して、元の local default と inherited packet を区別して形成する。PF1/PF2 は finite license proof を辿り、全依存 witness を保持し、GC の uniform local law を suspended Op として使う。candidate f の membership、license fiber の inhabitance、runtime authority を policy の存在から導かない。元の独立 primitive/arm/transition laws と foreign predicate の対応は残る。[固定版と査読](../tasks/agent-loop/sprints/name-recursion-profile-20261024-outcome.md)に合成の範囲を記録する。

### 4.14 原再帰例の全 native closure model

[具体的な再帰木モデル](../notes/theory/2026-10-24-explicit-recursive-native-model.md)は、原 argument-replay source の最初の公開直前までに発行される全三 seeds と全 ordinary variables を固定する。A=Record(a:Int)、G=μg.Function(Int,Record(first:j,next:g)) とし、K も含む全 endpoint の解釈を与える。NM1 は Seed/VarId/CutVar/Function/Record の全 closure 規則が bisimilarity を保つことを示し、NM2 は missing field・異なる constructor・Primitive identity の failure を排除する。これにより、GE6 の「C 全体のモデルがある」という前提を、この具体例では実際に除いた。

NM3 は C/B、D/J、T/Y の全 copy と全 cut に一つの valuation を同時に与える。これは finite pre-publication native interval の結果である。source の advertised result と j の実 projection、独立した公開後使用の coverage、combined termination は別の証明を要する。

[actual replay の source diagram](../notes/theory/2026-10-24-actual-replay-receiving-diagram.md)は、実 f entry で返った Record、fresh x、次の内側閉包の capture、後の実 invocation の Name x と h Call を全依存 field のまま接続する。AR1/AR2 は、旧 x を書き換える SC4 の誤りを避けて source 側の middle matching を構成した。前段が返らない場合は後段を未実行の suffix として残す。static Argument/Swap、ordered Replay と T/Y の生成記録も同時に照合した。

この後の native extrusion occurrence の receiving field を、その source diagram の h receiver と同一視する constructor correspondence は残る。AR2 の実 receiver と solver の field は別の対象であり、support 集合や upper route の存在だけでは同一性を証明していない。両稿の明記した結果は独立査読で受理された。[固定版と査読記録](../tasks/agent-loop/sprints/actual-replay-model-20261024-outcome.md)に未閉鎖の対応を保持する。

### 4.15 共通 h の二入力と実 client の逆向き輸送

[公開後の二使用](../notes/theory/2026-10-24-publication-reverse-coverage.md)は、原 argument-replay store の T/Y 等置を仮に行い、実 `succ (((f {a=0}) 0).first)` と Bool 側の同形 client を比較する。全 freshening clones、共有 C/D/T、八つの実 App/Sel result rows を列挙する。actual demands は Int≤Y₁ と Bool≤Y₂ であり、Y₁=Int/Y₂=Bool という追加等式はない。明示した structural preorder で全 closure を満たすモデルを作り、この client family の任意の等置前モデルから H/C/D/T を固定したまま等置後モデルを作る P3 を証明する。この family の可解性の逆向きが閉じ、任意 client の NL7 converse とは区別する。

[同じ h/f の source 二使用](../notes/theory/2026-10-24-two-input-recursive-source-use.md)は、U=Int|Bool、A=Record(a:U)、actual h₀=λz.0 を用いる。TU1/TU2 は ground data と genuine h₀、TU3 は NR の全四成分をこの U で再構成する。TU4 は実 f Return を monomorphic Name alias に結ぶ source Bind client を型付けし、同じ h/f/world で両入力を受け取れることを示す。独立 kernel/arms の元契約は残す。native nested-App とこの Bind syntax の全推論対応、通常 let の Generalize、actual T/Y 資格、全 source coverage はこの二つの結果を並べるだけでは得られない。この明記した範囲は独立査読で受理された。[固定版と査読](../tasks/agent-loop/sprints/publication-two-use-20261024-outcome.md)に一般 coverage との境界を記録する。

### 4.16 任意有限段の next 観測と出力契約

[有限 next 観測の公開輸送](../notes/theory/2026-10-24-finite-next-observation-coverage.md)は、root App、next/first 選択、後続 App、succ、有限 Record、共有 alias からなる定義済み client grammar を、有限深さ・分岐数の上限なしで扱う。実 next upper bounds と MonoBind の formal/result rows も残す。FN1 の guarded refinement と FN2 の構造帰納により、低い H/C/D/T を固定して全 client node を旧モデルの subtype へ修復し、固定された whole output upper contracts を保つ。これで P3 の next 未消費という条件をこの grammar では除いた。任意の高階 client、可変外部契約、全 source principality への拡張は別である。

[source の有限観測 phase](../notes/theory/2026-10-24-finite-observation-source-bridge.md)の FO1 は、元 callee 証拠と argument の whole-carrier checking から、同じ actual Return/provider、receiver/pending/future を構成する。FO2 は有限観測への合成を与えるが、returned U/A だけから argument 計算全体の checking を得たという初稿の適用には MAJOR 指摘があった。その無条件の主張を撤回し、各 edge の実 checking 証拠 χ_e を明示した条件付き結果として残す。一般 χ_e の構成、独立 computed-Call result descriptor への最後の DescMem、native Lambda MonoBind と source Bind の対応、一般化は未完である。[査読と訂正記録](../tasks/agent-loop/sprints/finite-next-coverage-20261024-outcome.md)に、受理された FN1–FN3/FO1 とこの残項を分ける。

## 5. 完了の判定

定理 C の成立により、生成済み核についての「有限 interface が適切」「内部 continuation が安全」という未構成の仮定は除かれた。次の作業は §4 の各 source/算法接続を構成し、1節の元の主張へ戻すことである。現段階で全言語・推論の証明が完了したとは報告しない。


### 4.17 let-free 高階 client と computed argument の carrier

[let-free client の構造的輸送](../notes/theory/2026-10-24-let-free-client-reverse-coverage.md)は、既存の regular-tree model と一意な Record labels の域で、原公開 root を使う全有限 Lam/App/Rcd/Sel/Var/Lit clients への reverse repair を構成する。Lambda formal の旧解を保持し、body と Record を共変に運び、App/Sel は旧 result を保持する。有限 next 観測だけに限られていた client grammar を高階関数へ広げる。元 qY=T、全 original/cloned bounds、低 anchor と固定出力契約を保持し、local-let 一般化や全 source/native 対応は別の元義務とする。この明記した範囲は独立査読で受理された。

[computed argument の whole-carrier 構成](../notes/theory/2026-10-24-computed-argument-carrier-checking.md)は、同じ実 h₀/f/g の raw code と TU の完成した membership を使う。finite source grammar の Call/first/next/Record/alias について、実際の引数計算の全 prefix と Return を構成し、元 Delay criterion の inert formation と全指定 Force を満たす。返却型から効果を消す推論は使わない。actual-source carrier の χ 成分を供給し、独立 W/Z 等がある complete interface 全体には、その同じ target への arm-local inclusion を別途結合する。

後者は FO2 の全 χ を無条件に証明したものではない。succ の complete primitive law、独立 arm の target-specific checking、computed Call の独立 result descriptor は残る。元の arbitrary-client/source parent と receiving/SCC 資格の未証明対応も保持する。両稿はこの範囲で独立査読を通過した。[固定版と査読範囲](../tasks/agent-loop/sprints/let-free-carrier-20261024-outcome.md)を参照。


### 4.18 local-let の公開と computed Call の result

[nonrecursive local-let の検討](../notes/theory/2026-10-24-nonrecursive-let-client-coverage.md)は、RHS の level+1 推論と、低い captured context へ生じる実 extrusion、公開後の freshening を対象にする。let-free の構造帰納だけでは、保存された bound graph に現れる低いコピーの解まで保持できるとは限らない。全 finite local-let clients への拡張は未閉鎖。実 `lambda k. let a=k f in a` について六つの before コピーと五つの after コピー、全 bound と出力を保つ repair は独立査読で受理された。消える y は恒等 row 対応の誤りを示すもので、coverage の反例ではない。

[computed Call の Bind result](../notes/theory/2026-10-24-computed-call-bind-result.md)の初稿は、relation/interface graph を complete descriptor に昇格させる規則が未供給と査読され、その無条件な CB2/CB3 を撤回した。CB1 の post-CalRet phase 証明と actual operational composition は受理された。

欠けていた規則は [新しい EvalInvoke definition](../notes/design/2026-10-24-computed-call-result-constructor.md) で明示する。実 callee computation、内側で束縛される CalRet、argument formation、同じ provider の complete receiver を、元の順序・full fields のまま解釈する。これは旧規則からの自動導出ではなく、新 generated-result constructor の定義である。EI-Intro と checked immutable read C_Read(F,n) における元 ReadInvoke への両方向 specialization、全 independent arms の保持は再査読で受理され、primary がこの生成 constructor case を選択した。固定 foreign R_c、native result-slot の sort/scope 対応と全元親義務は残る。

[今回の統合記録](../tasks/agent-loop/sprints/computed-result-definition-20261024-outcome.md)に、初回 MAJOR、明示的な新定義、再査読の固定版と全体未完了の境界を保持する。


### 4.19 nested let のコピーと生成 result view

[polar copy と nested publication](../notes/theory/2026-10-24-let-polar-publication-simulation.md)は、元 selected-bound copying の必要不等式を LP1 として明示し、二重の nonrecursive Let で実 high/low 境界を追う。内側で low だったコピーは外側の公開では high となり、二つの使用で独立に freshen される。LP2 は永久 low 分類を反証するが、同じ実 graph の共同 repair も与えるため coverage の反例ではない。一般 LET-POLAR-PUB はまだ未証明である。

[generated computed result の対応](../notes/theory/2026-10-24-generated-computed-result-correspondence.md)は、選択済み EI を元 Call の実 operand と IF slots から形成し、定義された ViewLogic として同じ source occurrence に付ける。GR1–GR3 は complete sort、元 event binder の内側の依存、有限登録 graph、whole substitution、actual result/provider/current-world/future の一致を構成する。GR4–GR6 は genuine local inputs を持つ元 source proof にその view を付加・消去する。元 `Comp(E_c,A_c)` と CIncl は保持し、EI の導入だけで target checking を削除しない。

この source 構成は、既存の全 native result rows が EI を符号化するという証明ではない。全 Let の signed bound/publication transport、fixed target の実包含、primitive/arm laws、source/native receiving 対応と元の全親義務は残る。両稿はこの範囲で独立査読を通過した。[固定版と査読範囲](../tasks/agent-loop/sprints/let-polar-result-slot-20261024-outcome.md)に全体未完了の境界を記録する。


### 4.20 全 nonrecursive-let client の signed updates と段階 extrusion

[signed update と extrusion の段階合成](../notes/theory/2026-10-24-signed-update-extrusion-corridor.md)は、固定fの全有限 nonrecursive-Let clientsで、P/N/Zの相互文法とactual bound-list invariantを構成する。SU1–SU4はsource seeds、片側insertion/replay、Functionの反転、両listのfresheningを同時に保つ。SU5により、Y系の全コピーのupperは共有Tのままで、clientから別のupperを追加されない。従来のLET-POLAR-PUBに残っていた、このsigned-update義務を一般に閉じる。

EC1は任意のfinite level-closed storeで、二段extrusionの全modelを一段extrusionへ運び、元row値とextruded resultを保つ。EC2は二つのtarget levelsの間にある固定publication boundaryと任意有限個のfresh instancesへ拡張する。中間copyの各useを等置せず、共有lowを一つに保つ。

元history全体との合成は未完である。Variable branchの優先順位とcache hitにより、保存されたL≤Y≤TというpathだけではL≤Tの最新処理を主張できない。介在する更新、消えるY.lower到達部分、全historyの一つのmodel actionが残る。固定snapshotのEC2を任意interleavingへ一般化したとはしない。本稿はこの範囲で独立査読を通過した。[固定版と査読範囲](../tasks/agent-loop/sprints/signed-extrusion-corridor-20261024-outcome.md)に元の未完了義務を保持する。


### 4.21 Let/LetRec の全元履歴を保つ共同モデル

[有限 let 履歴の canonical model](../notes/theory/2026-10-24-canonical-let-history-model.md)は、全 f-role descendants の実 internal/external clause origins と完成時の production bounds を追う。client が新しい recursive Let を含む場合も、実 Z placeholder、monomorphic recursive lookup、RHS≤placeholder、返却後の publication から signed invariant を追加証明する。全 J/R/o の下界と B/Y の上界から、同じ guarded regular value G* を使う同時 depth 帰納を行う。

これにより、固定 f/P1 domain の任意有限 Let/LetRec 元推論履歴の全 copies を一度に canonical values へ修復できる。全 client Z の値、元 bounds、source seeds、出力契約、実 mutable publication/use snapshots を一つの model で保つ。各 snapshot で新しい model を選ばない。全 Y descendants=T（および明示した同役割等式）を追加しても、全 Z coordinates 上の solution projection は変わらない。

これは元履歴の joint repair を閉じる。早い段階で intrusion した別履歴の新しい Z copies、level lowering と共有、全 actual events の対応はまだ構成していない。source/native receiving/SCC と元全 A/B、principality、termination も残る。CH0–CH7 は独立査読を通過し、コピー完了点の定義を MINOR 指摘に合わせて明確化した。追加 CH8 は、実 Y.lower entry の低い T-boundary factor と、その同じ低い項を共有する両 list freshening を構成する。CH8 も独立差分査読を通過した。新 after copy の全 selected bounds と polar memo の合成は残る。[固定版と査読範囲](../tasks/agent-loop/sprints/canonical-let-history-20261024-outcome.md)に受理した命題と残項を記録する。
