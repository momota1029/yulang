# Cycle128: raw dictionaries, computed frames and full nominal source evidence

**一般sourceのB4Bridges V3: 未充填12 / 全12。一般B4は未完成。**

開始2026-11-11T23:27:19Z。検証・途中成果公開・報告・writer解放を含む期限は
2026-11-12T00:22:19Z。文書の実装時間指示より最新ユーザーの55分総上限を優先した。
確定した終了時刻と所要時間はcompleted heartbeatへ記録する。

## 今回閉じた部分目標

1. **raw payloadから全source義務を復元（約23:32–23:40）。**
   Checked registryの実宣言を検索し、各nodeのcanonical子を計算する。呼出側から渡していた
   再帰source occurrence recipeを除去した。欠けた子と余分な子を両方拒み、zip切捨てや
   deduplicationで成功にしない。既存の独立Plan Evidence＋Readbackとの正確なiff、
   raw PayloadEvidenceの存在とのiffを証明した。これは宣言Planに対する完全性であり、
   head適用性・role解決の完全性ではない。
2. **元payloadと意味を同じtreeへ接続（約23:34–23:40）。**
   localize、headless prepare、source prepareが完全source treeを保存することを証明した。
   以前の「返却辞書の消去payload」だけでなく、今回入力したraw payload自体について、
   一つの固定source witnessが全joint modelで独立Instanceを持つ。
3. **任意full nominal assignmentへの意味拡張（約23:39–23:50）。**
   新integrationのAstra nominal carrierを使い、既存dictionary等式、実head/RHS意味と
   capture実現を任意nominal assignmentへ接続した。Commonからのliftだけに限定しない。
   nominal73という具体値の同時modelを示した。この値が既存Intの埋込みと違うことも証明した。
   nominal-pattern compilerを実装した意味ではなく、変数patternがnominal値を捕まえる範囲。
4. **full nominal stateへのdictionary記録（約23:45–23:48）。**
   型sourceとrow sourceを別に持ち上げ、full stateのglobal ordinaryへ全有限batchを追加する。
   元のnominal descriptor・view・source ownership・全既存制約を保持する。新Modelsは元Modelsと
   全dictionary等式の連言に正確に一致する。任意modelの元state保持と全source Evidence、
   package順のmodel不変、記録前後のRootPending同値を証明した。一般Stepではない。
5. **candidate reportからFramesを計算（約23:48–23:55）。**
   実visible宣言と既存arguments/reportからcaptureを計算し、Astraのallocation/identityをそのまま使う。
   既存Survivorならこのcomputed frame上のPlanとなる。全nodeのcandidate Evidenceがあれば、
   外部Framesなしにraw payloadから一意のsource witnessを復元できる。
   existing Display→terminal Int fixtureで実childのidentityと完全demandを保持する回帰を追加。
   この回帰のleafはPlanであり、leaf Survivorを証明したという主張ではない。
6. **candidate/source両証拠の同じ返却木への結合（約23:53–23:55）。**
   同じContextにおける独立raw Candidate Evidenceとsupported-variable準備成功を前提に、
   実返却辞書そのものがcandidate Evidenceを保持する。同じ一つのwitnessが元Readbackを持ち、
   全full記録modelで元Modelsと独立source Instance Evidenceを同時に満たす。

7. **結合した全前提の同時成立（約23:55–00:02）。**
   key7、変数head、既知source slot1、root outputs=[]のchecked終端宣言で、既存の全guardを
   満たす実Survivor、raw candidate Evidence、計算Framesの準備成功、具体full記録modelを
   同時に示した。その同じ入力からcandidateと独立nominal source両Evidenceを持つ一つの
   Readback witnessが返る。条件付き橋の成功前提が空ではない。一般入力の存在証明ではない。

25分時点ではnominal部分の公開、candidate/source結合の最終回帰と検証・報告が残っていた。
最初の部分目標で終了せず、一般B4のevidenceNodeに必要な入力削減とmodel範囲の拡大へ進んだ。
終了理由はI-15(a): 約50分の総作業内で最終検証・公開・報告まで行うため。

## 復元・担当・制限

- integrationを開始時にca1013dedへ更新し、standing orders/inboxと公開済みcycle127報告・heartbeatを読んだ。
  前writerは8f5e1fd4aでcompleted/released。並行writer・crash復旧・未公開source喪失はない。
- 作業中にintegration6e1e848へ進み、Astraのnominal8moduleを取得・統合した。inboxは同hash/ACTIVE。
  旧報告のmerge競合は公開済み最終報告を保持した。既存Leanソースの改変はしていない。
- dotはI-18項目5のみ。Astra項目1/2/3の実装、未割当項目4、spec/plan/lakeは変更していない。
  新dictionary記録は既存extendを使う有限transactionで、一般Stepや需要併合の実装ではない。
- 初回heartbeatは前writer確認と文書読取後の23:32に公開。以後10/20/30/40分付近と途中公開で更新。
  最初のheartbeatには開始から約4.7分の遅れがある。後続時刻はpublished heartbeatに残す。
- 同じContextで全nodeのSurvivor証拠を仮定するadapterである。child private-state列や安定snapshot、
  finite candidate forest自体の存在はまだ導いていない。
- root、raw selected-key payload、Contextが入力として残る。一般候補選択・完全materializationではない。
  variable compilerは同じcaptured endpoint IDと既存base slotを必要とする。
  nominal/compound/default RHS、非singleton区間、新reserved identityのbase slot化は未接続。
- root.outputs=[]・freshness・coverage・pendingなど既存candidate guardは一切緩めていない。
  独立Instanceへの一方向健全性を無条件iffに変えていない。任意inputのmodel存在も主張しない。

## SourceBoundary全13項目

| Field | 状態 | 今回の位置と残り |
| --- | --- | --- |
| Checked | 一般宣言certificate定義あり | Astra所有。complete checkerの境界を維持。 |
| Models | 一般full nominal state定義あり | 今回dictionary記録と全nominal modelを接続。完全role model/boundaryは未完成。 |
| Step | MISSING | 一般進行・I-20需要併合。未割当なので触れない。 |
| Stable | MISSING | EOFと兄弟fixpoint。 |
| Generated | 一般emission/Plan部品あり | rawから完全canonical子を復元。driver由来の一般生成ではない。 |
| RootPending | 一般partial定義あり | 全無名引数のknownness。dictionary記録でもpendingを保持する回帰。 |
| RootK2 | 一般partial定義あり | nominal/structural全coneの対応はAstraの境界を維持。 |
| CandidateK2 | 一般carrier上partial定義あり | source provenance、全inspection/materialization範囲を満たす完全fieldではない。 |
| InspectionPending | 一般carrier上partial定義あり | unsupported coverageを残す。dotで変更なし。 |
| Survivor | 一般carrier上partial定義あり | 実reportからcomputedFramesへ橋渡し。root.outputs=[]等のguardを保持。 |
| Evidence | 一般carrier上supported-variable定義あり | raw→source、任意nominal model、full state、同返却木のcandidate/source結合まで。完全boundary代入は未達。 |
| Reorders | 一般構造定義あり | 固定root/raw payload/frames/stateのOption結果不変。異なる最終state/driver順は未達。 |
| DictionaryEquivalent | 一般source/payload構造定義あり | 今回は完全tree等価で接続。一般boundaryの観察意味は未接続。 |

## 量化子・検証・公開

[全公開定理の正確な型と日本語の主張](dots-cycle-128-theorems.md)に、量化子と前提を省かず記録する。
[検証記録](dots-cycle-128-verification.md)に、実行コマンド、focused build、scoped audit、
diff-only gateの出力全文とexit code、公開tree照合を記録する。

最初のcheckpointはfb39cf4a314119199a69ab6e042832afd5f42455。6module/34定理、
2474 tracked files全件一致、hosted core/proof success。proof logのcheckout SHA一致、
full1429jobs、9053audit entries、今回34/34名前と許可外公理0を確認した。

第二checkpointは693411e672eff43f3edeb28278a7ded8a0401420。14module/77定理、
2482 tracked files全件一致、hosted core/proof success。proofは1437jobs、9096audit entries、77/77追加定理、許可外公理0。
いずれもGitHubアプリのblob/tree/commitと非force expected-head更新でwork/dots-mainだけに公開。
local full build、local全Audit、独立AxiomGateは実行していない。hosted結果と混同しない。

## Yulang2照合・質問・次の接続

work/dots-auditを取得し、y2-claims-role-boundaries-cycle-2.mdのROLE-MORE-001–008と
対応する実機結果を読み直した。旧advertised-whereは新specの候補前提と異なるため輸入しない。
正本はspec06§6.3のwhere連言・兄弟安定後解決・output-only・全入力knownnessである。
新Yulang2実機試験はしていない。今回は新言語意味論の選択が不要で質問ノートは0件。

次の候補:
1. 固定Contextの再帰candidate証拠ではなく、実child private-state列からdictionary入力を導く。
2. nominal candidateのreserved/global sourcesとdictionaryのbase-slot materializerの間を接続する。
   freshnessとorigin ownershipを保持し、予約されたsourceを勝手に既存slotへ同一視しない。
3. root associated出力・compound/default RHSの一般source意味を、担当Astraのcoverageと整合させる。

開始/途中空き37GiB。cacheコピー・削除なし。使用量上限は不明。
修正前のelaboration/linter failureは成功に数えず、最終greenのログと区別して記録する。

## 最終source公開と検証結果

最終source commit: `07cfd9def3a1eb5baf7b21fb600659b4d98d21d2`。
Tree: `f4c14547520c0c3098cbf0bbb056a5a05c1c1749`。新規17module、公開98定理。
GitHub recursive treeの全2485 tracked filesをlocal検証treeとpath/mode/type/blob SHAで比較し、
全件一致、truncated=false、差分0。報告公開では、この検証済みLean sourceの各blobを変更しない。

- focused build: 603jobs成功、exit0。範囲は本cycleの17moduleと依存のみ。
- scoped audit: 全98定理、exit0。正確な型98件、exit0。定義7件の公理監査もexit0。
- diff-only gate: exit0。出力全文は検証記録へ。
- 実行評価: raw producer→some(2,2)、子欠落→true、実computed candidate frame→some(1,2)、
  同時成立fixtureの実prepare→some(7,1)。trust0でexit0。括弧は根keyと観察node数。
- [hosted core](https://github.com/momota1029/yulang/actions/runs/43124544032): success。
- [hosted proof](https://github.com/momota1029/yulang/actions/runs/43124545197): success。
  proof job130873179892のcheckout SHA一致。full1440jobs、9117audit entries、
  今回98/98定理を確認し、全logで許可外公理0。これはremote CIでありlocal full buildではない。
- 独立レビューで意味範囲・固定Context・変数限定・guard維持・条件付き前提を再確認。

公開はwork/dots-mainのみ。最終報告commitとcompleted heartbeatは同branchで確認できる。

## 次の橋の具体的分解（約00:08–00:11）

[typed slot coverageとcomputed-frame orderの設計ノート](../design/2026-11-12-cycle128-next-bridges.md)
を追加した。これは新しい定理・実装ではない。

- nominal `Linked`はreserved/global IDへの所属まで含むが、dictionary `Available`は実際の
  base.type source slotを必要とする。既存nominal `extend/propagate`はbaseを増やさない。
  従ってそのLinkedだけから成功を導かない。次は明示的なtyped finite coverageと、型/rowを
  区別し旧slot・global assignmentのfull nominal Modelsを保存する拡張certificateが要る。
- 固定Context・checked registryのcomputedFramesは、宣言/where順の変更で同じになると
  見込まれる。reportはheadに依存し、source IDはpersistent seedとstable originに依存する。
  absent lookupを含むbindings等価を先に示す具体的proof routeを記した。未証明である。
- 新row source mappingやdistinct endpointの同一視を勝手に決めない。一般Stepは別担当の
  未割当項目であり、ここで実装したことにしない。

## 公開後照合と終盤の追加確認

報告commit `e4735542a4f2a9c6951d2fdef7cef4c5c4e57c16` は全2489 tracked filesを
path/mode/type/blob SHAで再照合し一致した。主報告・98定理の型・検証ログ・次橋設計を
個別に再取得し、blob SHAと型一覧98件も確認した。その後の追記も同じ方法で照合する。

00:13–00:15には次橋の不足を、既存fixtureにID1000を予約するだけの独立probeで確かめた。
nominal Linkedと元full modelは成立する一方、base Availableは成立せずlocateはnone。
4つの匿名例をtrust0で検証した。公開定理98件にはこの一時probeを含めない。

終盤の再取得でintegrationは`07152a05496ecc1f69ed7bf769bd44db02141e46`へ進んだ。
このcommitは本cycleの公開source/報告と追加のAstra nominal成果を既に含む。
inbox/standing ordersは6e1e848時点から変更なし、ACTIVE。55分総上限の終了処理中のため、
追加Astra成果のローカル統合・再検証は次cycleへ送る。今回の成功結果は明記した
source07cfd9dと検証base6e1e848に限定し、新integration全体のlocal検証成功とはしない。
