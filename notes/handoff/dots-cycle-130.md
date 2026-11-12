# Cycle130: recursive source Evidence, its exact obstruction, and recorded repair

**一般sourceのB4Bridges V3: 未充填12 / 全12。一般B4は未完成。**

開始2026-11-12T01:27:19Z。55分総上限の期限は02:22:19Z。
検証・公開・報告を含む確定所要時間はcompleted heartbeatに記録する。
新規10modules、公開89定理。25分時点ではpositive repair、完全なsource意味の順序不変、Metadata reviewと最終検証が残っていた。

## 重要な結論

現行のrecursiveFieldsで、正しいsource Evidenceを定義するだけではV3のevidenceNodeは閉じない。
**このフィールドの現在の全state量化は強すぎる**ことを、checked・safe・uniqueな実終端候補と実モデルで証明した。
関連型の出力を無視したEvidenceや、存在するbranch modelを全modelの代用品にする証明は採用していない。

具体例は、`impl Container (list 'a): type item = int` に対する `Container(list α, item = α)`。
元のstateはα=strを許す。α=intなら候補branchのモデルになるため候補は一つだけ生き残る。
しかし元のstrモデルでは宣言のitem=intが偽になる。悪いモデルでもprivate head intervalとprojectionは成立しており、失敗は要求された関連型出力に局所化される。

`no_evidenceNode_of_output_sound`は、この実output等式を守る**任意のEvidence実装**についての阻害。
`no_evidenceNode`は今回の具体的Evidenceへの特殊化。どのStep/Stable/Generatedを選んでも、この全stateフィールドの型は変わらない。
これは飽和後Σ*のモデルで述べるB4主張を否定していない。`no_dictionarySound_of_unchanged`も、executorがこの未更新contextをそのまま返す場合だけを否定する。

監督役向けの[質問ノート](../questions/2026-11-12-cycle130-evidence-node-state-scope.md)を公開した。
推奨する遅延案は既存V3を残し、最終状態または候補制約の記録が証明された状態に限る新しい局所橋をレビューすること。dotはtarget・意味論・Astra定義を変更していない。

## 閉じた部分目標

1. **Recursive candidateから実source辞書を復元（01:33–01:39）。** recursive reportからFramesを計算し、raw key/child payloadから完全なsource occurrence treeを復元する。反復capture、全childのidentity・順序・重複を保持。candidate derivationは前提で、森林を自動発見したとは主張しない。既存supported-variable準備とrecord後全modelのsource意味へ接続した。
2. **モデルごとの独立source Evidence（01:34–01:49）。** visible checked declaration、実canonical child列、Finished/RequestReady、Metadata、指定モデルでのprivate interval・projection・materializationを持つInstanceを定義。Survivor/Classify/executorを定義に使わない。全childと親は同じモデルで証明する。inspection-mediatedな証拠であり、一般ground Pattern意味の別個の完全性は未証明。
3. **全state橋の形式的阻害（01:34–01:51）。** checked terminal fixture、safe/unique/classified、good branch、bad original modelを同時に構成。source output lawを守るどんなEvidenceも現在のEvidenceNodeを満たせない。一般B4の完了扱いを防ぐ具体的な型の問題を特定した。
4. **記録による正確な修復条件（01:45–01:54）。** fixtureのBranchModelsとsource Evidenceを、それぞれ元Modelsかつoutput=intと同値にした。既存ordinary atomの2不等式を実際に追加すると、非空かつ厳密に小さいモデル集合になり、その集合と固定辞書のEvidenceが同値。実source更新driverや選択方針の実装ではない。
5. **非point・反復captureの意味（01:43–01:53）。** 指定branch modelの実観察値が、同名binderの全intervalを満たし、その併合captureおよびvariable where childを満たすことを証明。追加cross/merge/self/projection/materialization条件を元Modelsから分離した。
6. **辞書意味の順序不変（01:49–01:56）。** fixed Contextでchecked visible/where列を変えても、canonical materialization requests、BranchModels、Instance、indexed/raw Evidenceが同じassignmentと同じsource witnessを保つ。computed Framesと復元/準備のOption全体も不変。driverの最終state間の同値ではない。
7. **constructor意味の整合性をレビュー（02:00–02:02）。** InstanceがMetadataを保持するよう強化し、全影響箇所を再build・再audit。候補Preparedから導ける既存guardなので、node theoremの前提を追加でcallerへ押し出していない。早いcheckpoint70a009ecはこのguardをまだ保持していなかったため、最終source4c84d2fcを使用する。

最初の阻害で停止せず、正しい条件付きEvidence、実記録の正修復、実source readbackと順序不変まで進めた。
残る一般evidenceNodeは設計レビュー待ち。終了は55分総上限内の検証・報告・公開完了を含む。

## 復元・担当境界

integrationを`9230c133c9627cab9504fa6c26a644c9fd9f6ad1`へfresh fetchし、standing orders/inboxを読み直した。ACTIVE I-21、前cycle129はcompleted/released。writer重複、crash復旧、未公開source喪失はない。
local mergeの競合は監督役integrationを優先し、作業はその上へ追加した。既存Lean実装・spec・plan・lake configは変更しない。追加10modulesとYulang/Audit/README追記のみ。
Astra担当Step/Stable/Generated/I-20には手を出していない。recorded fixtureは既存extendの局所例でありStepを定義していない。

## SourceBoundary 全13項目（検証基準9230c133c）

| Field | 状態 | 位置と残り |
| --- | --- | --- |
| Checked | 一般定義あり | Astra既存certificate。 |
| Models | 一般定義あり | 同一full nominal carrier。BranchModelsの追加条件を明確化。 |
| Step | MISSING | Astra担当。未変更。 |
| Stable | MISSING | Astra担当。現EvidenceNodeはこの前提を持たない。 |
| Generated | MISSING | canonical emission部品あり、driver接続はAstra担当。 |
| RootPending | 一般carrier上partial定義 | 既存root入力readinessを保持。 |
| RootK2 | 一般carrier上partial定義 | mixed recurrence coverageの境界を保持。 |
| CandidateK2 | 一般carrier上partial定義 | 未変更。 |
| InspectionPending | 一般carrier上保守的定義 | unsupported inspection/materializationを残す。 |
| Survivor | 一般carrier上partial定義 | Astra recursive Survivorを変更せず使用。 |
| Evidence | 一般carrier上のpartial source証拠を定義 | Metadata・実branch条件・全children。同一model。無条件nodeは阻害、ground-pattern完全性は未達。 |
| Reorders | 一般定義あり | fixed Contextでbranch/source Evidenceまで不変を証明。driver順は未達。 |
| DictionaryEquivalent | 一般構造定義あり | 既存payload equivalence。今回同じsource witnessを保持する。 |

## 検証・公開

最終source: `4c84d2fcb0b8fc71cfe625178a4ba3562a126998`。tree: `e1b5b75ae0bff4a9932e459fa881106a59bed3eb`。
全2544 tracked paths/modes/types/blob SHAを照合し差分0、truncated=false。
focused buildは620jobs、全89定理のscoped axiomsと全型取得がexit0。
使用公理はpropext/Classical.choice/Quot.soundのみ。最終Metadata強化後に再検証した。
実行probeはreadback=`some (300,40,0)`、legacy variable-only preparation=`false`、記録atom数=`2`。
前者はnominal headを持つ実候補のsource復元。後者は旧compiler制限であり候補rejectではない。

全コマンド・出力・終了コードとhosted CIは[検証報告](dots-cycle-130-verification.md)。
各定理の正確な全量化と日本語の範囲・健全性等の側は[89定理一覧](dots-cycle-130-theorems.md)。
全体lake build/Audit/AxiomGateはlocalで実行していない。hosted結果はlocal focused結果と区別して記載する。

## Yulang2との照合

work/dots-auditを取得し、ROLE-MORE-001–008を確認。旧advertised-whereの挙動を新specへ輸入しない。
今回の根拠はspec06§6.3の関連型等式、where連言、安定後の最終化と承認済みB4草稿第4項。
新しいYulang2実機試験は実行していない。意味論の新決定は0、形式化のstate範囲について質問1件。

## 次に必要な仕事（I-21の範囲を勝手に変更しない）

1. 監督役がevidenceNodeの最終state scopeをレビューし、既存V3を残したまま適切な局所橋へ接続する。現在の全state橋を正しいsource意味のまま証明することはできない。
2. Astra側の更新が全selected nodeのordinary/projection/materialization条件を実際に記録することを証明し、同じ最終modelで全childを結合する。各nodeの別々の存在modelでは不足する。
3. independent ground-pattern semanticsと現inspection-mediated Instanceの対応、nominal/compound/default RHSの一般materializerを拡張する。legacy variable-only準備のfalseを成功扱いしない。

空きディスクは開始時37GiB。既存cache全体のコピーや削除はしていない（検証用worktreeは別途使用）。使用量上限は不明。

## 終了直前の上流更新

02:10台のfresh fetchでintegrationが`3fcd14ec614aaf04af1e0bb7fffec30fefcf59bd`へ進み、I-22（循環の上にある根のK2）と新しいAstra飽和部品を確認した。inboxはACTIVE。今回の最終source/CIは9230c133cを基準とする。検証後の意味論を無検証で取り込まず、次cycleへ引き継ぐ。新しいcycle-based K2について「拒否需要に辞書を作らない」の適合証明は今回未完了。上のStep等の未定義表も今回の検証基準に対するもので、新上流に存在しないという意味ではない。

I-22の境界を追加reviewした。SafeKnownは¬RootK2と¬CandidateK2を含み、V3 Classify.selectedは各nodeでこのguardを必要とする。一方、raw reconstruct/prepareにはK2 guardがなく、SurvivorもRootPendingだけを除外する。Instance/Evidence自体は意味の証拠で選択policyではない。したがって公開辞書emissionをselected classificationへ接続し、Astraの新しいcycle predicateでlen(nest0)/len[loop1]を検証する仕事が残る。raw APIにK2拒否保証があるとは主張しない。
