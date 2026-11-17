# dots cycle234 — mixed trusted cache を実kernelへ接続した飽和回帰

開始: 2026-11-17 06:30:41 UTC。研究・量化子レビューは07:15頃まで（約45分）。検証・公開照合期限07:25:41。
前周233はcompleted、報告・公開f9c0afbeとlocal treeが一致し、競合プロセスなし。
復旧作業は不要。初期integrationはbc61dca49。
06:56に最新integration05c575b4022bb1f71b29d39c3836e2c6efb4ce19を再取得。
standing-orders/inbox変更なし、I44有効、STOPなし。統合を取り込んだ。
barrel/INDEX/233 designの競合は、統合の全行が手元の後続追加に含まれることを
照合して解消。既存Lean意味コード・凍結Audit.lean/README.mdは変更しなかった。

## 中心結果

233の新trusted cacheは補助層だった。今回は**実mixed kernelとsource boundary**へ接続した。
Installable.cache、administrative/direct refresh、reobserveの全箇所を同じmixed interfaceに揃え、
既存の候補・cycle・choice・complete materialization・共通モデル等のguardは落としていない。
モデルの保存だけでなく、実際にこの追加の観測能力を使う経路を構成した。

### I44 / 230 の例

`GeneralDictionaryMixedClosedRegression234.positive_regression`:
原source初期状態→旧版の新install→point reobserve→新版の新install→mixed refresh、という
**実4step**の終点で、checked・source Reachable・**全mixed Stable**・実selected・
literal EvidenceAt・非空Models＋辞書evidenceを同時に満たす。
さらに `all_models_evidence` は**全終点Models assignment**に辞書を構成する。

refreshは原5slotに3slotを追加し、旧版hi・新版lo・新版hiをWとして実際にKnownにする。
古いlo=Oと新しいlo=Wは同じjournalに残り、名前を混同しない。
source identity、seed、元の0..4、actual中心、plans/effectsも保持。
単に旧Stableを引き継いだわけではない。旧233の終点はmixed kernelでは実refreshが残ることを
`MixedUpperStep234.not_stable` / `MixedClosedStep234.not_stable` で示してから、
刷新後の全enqueue/refresh/reobserve/equate/install/mergeを改めて排除した。

### 206 default の例

旧install直後には、fullModelsで0≃1なのにraw側にはまだ等式がなく、実equateが可能。
`Gap206Feedback234.not_stable` はその早すぎる終点を明示する。
既存233でそのStableを完了扱いしていたわけではない。

equate後は旧Kernel232でStableになるが、新mixed cacheではdefault出力のInt頭を学ぶ
実refreshがさらに可能。最終的に `GeneralDictionaryMixedGap206Stable234.regression` で
**source初期化→install→equate→refreshの実3step**、非空Intモデル、bottomモデル排除、
全mixed Stable、current selected、literal EvidenceAt、全Models current Evidenceを証明した。
この追加進行はEvidenceNode反例ではなく、強化した実kernelに必要な通常stepである。

199拒否・202default・204joinもmixed source boundaryの実Initial/非空Models/全Stableと
rejectedまたはselected・literal EvidenceAtへ移した。199のEvidenceAtだけはselectedが
排除される拒否例なので空虚であり、辞書が立つ例とは呼ばない。
218は原sourceからの実parent installと非空モデル・child生成、共有不整合の意味論核まで。拒否分類は未完。下記の節で条件を明記する。

## 一般の補題と量化子

全新宣言の名前・位置は `notes/verification/cycle234/declaration-index.txt` に列挙。
以下の「補助」はM1全体の健全性/完全性/主型性の完成を意味しない。

### kernel / source interface（健全性・局所分類の補助）

- MixedKernel234: 任意roles/registry/root/stateの全guard付きStep。任意Stepと後Modelsから前Models、
  任意Stepsのモデル制限、no-next-stepからrootと全Generated子のStable。
  任意旧232 Installable/Administrative/At/Step/Stepsを新へ埋め込む。
  Stableは**新→旧**のみ。旧→新の無条件移送は定義も主張もしていない。
- MixedBoundary234 / MixedSourceBoundary234: source registryを既存HeadAllocでcompileし、
  元のsource Initialを保持。診断/証拠の意味は232と同一。
  checked/initial/reachable_compiled、Local total/functionality、モデル保存・closure等。
- MixedSourceFrontiers234: 任意checked registry/state/rootのfrontierLocal、任意registry/stateの
  localIdentity。frontierの選択はClassical.chooseであり、実行可能executorではない。
- MixedEmbedding234: 任意旧source Reachableから新source Reachable、Local同値、
  任意新source Reachableのcurrent mixed CacheSoundとeffect-plan Recorded。
- MixedEvidenceTransport234: 同一stateのModels/Evidence同値、新Stable→旧Stable、
  任意の旧EvidenceAtから同じ点の新EvidenceAt。旧reachabilityは仮定不要。
  **EvidenceNode全体の移送ではない**。新Reachableが旧Reachableとは限らないため。

### 保存と安定性分解（健全性・停止性への補助）

- MixedGrowth234: 任意全kind Step/StepsのMonotone、source contextとseed保存、
  plans/effects/sites/edges/requestsの包含、Generated保持。任意source Reachableの
  実initial由来とcurrent/source seed一致。
- MixedRegistry234: 任意新source Reachableでregistry provenance、legacy plans/effects空等を保持。
- MixedKernelCache234: 任意新Step/Stepsでcurrent CacheSound保存、任意Reachableで成立。
  refresh/reobserve後は証明書の新snapshot cacheを使い、旧snapshotだけの保存にしない。
- MixedRecorded234: 任意source Reachableで、記録effectのplanがplansにある。
  任意Reachable/fullModel/記録effectから、そのplanのfullHoldsを回収する。
- MixedTerminalStable234: singleton raw/center sites、edges空、PointClosed、HeadlessUnknown、
  EqualityClosed、任意enabled installのCommittedという**明示条件**から全mixed Stable。
  HeadlessUnknownは実fullModelが存在し、そのmodelでsupported未知identityのどの頭testも
  成立しないこと。条件自体を結論の言い換えにしていない。
- MixedRefreshEquality234: 任意mixed Refreshと前EqualityClosedから後EqualityClosed。
  fullModels iff、support包含、raw Refinesを別々に使用し、等式閉包を結論仮定しない。
- MixedStableTransfer234: 旧Stable、実legacy currentCache、PointClosed、HeadlessUnknownの
  四条件から新Stable。199/202/204では四条件を具体証明した。
- VersionedEquate234: 任意stateとKernel.Equalの下で、equate前後の全assignment Models iff、
  追加した対のRawEqual。一般停止尺度ではない。

### 230 のcurrent packetと飽和（回帰、健全性補助）

- MixedUpperPlan/Semantics/Transport/Frame/Evidence234: まず6slot版で、inspection reportと
  bindings/capture/binder/schema/variablesを正確に比較。任意modelの旧fullHolds＋新rawModelsから
  新fullHolds、Prepared/Frame/Unique/Ready/ClassEffects、全Models Evidenceを構成。
  旧certificateを結論として仮定しただけではなく、journalの記録planから回収する。
- MixedUpperStep234: 実source経路後の新upper頭学習、全Models iff、非空Models/cache、
  source/plans/effects保存、旧終点のnew not-Stable。6slot終点のStableは主張しない。
- MixedClosedBase/Snapshot/Trust/Refresh234: 8slot版のinjective source embedding、
  source/seed等保存、旧hiは初版input trusted slice、新lo/hiは次版sliceからWを導く。
  全mixed Refresh guard、全assignment Models iff。
- MixedClosedPlan/Semantics/Transport/Frame/Evidence234: 8slotでも任意model量化のfullpacket移送と
  current certificate/evidenceを再構成する。Frameが受けるHoldsは先に非循環に供給する。
- MixedClosedStable234: 具体モデルを保持し、未知sourceはtopまたはOのみで頭がないこと、
  PointClosed、raw等式閉包、全current候補Committedを証明して全Stable。
  `halted` はこの一点のno-Stepで、一般executorのhalted橋ではない。
- MixedClosedSelected/Regression234: 実8slotのraw cycle排除をrankで証明し、全cycleと
  diagnostic conflictを排除してcurrent selected。Generatedがrootだけと一意分類から
  literal EvidenceAtを構成。全前提を同時に満たす具体モデルを添付。

### 206 と保存した回帰（回帰、健全性補助）

- Gap206Feedback/Selected234: install直後の実equate、非Stable、current selected/EvidenceAt。
- Gap206After/AfterSelected/AfterStable234: equate後のfullpacket/frame、全Models Evidence、
  legacy fullStable。新mixed終点とは区別する。
- MixedGap206Trusted/Snapshot/Refresh234: default出力をversioned trustedで読み、slot0のInt頭を
  学習するmixed Refresh。全Models iff、実source Reachable、Int保持/bottom排除。
- MixedGap206Frame/Evidence/Selected/Stable234: 現在のsnapshotでpacketとFrameを再構成。
  rawModels→fullModelsから等式閉包、全supportedsourceがKnownで追加refreshなし、
  install/merge等も排除し、fullmixedStableとcurrent selected/EvidenceAtを証明。
- MixedConflict199/Default202/Join204234: 原sourceのInitial、非空モデル、全sourceKnown等から
  一般StableTransferの四前提を埋め、各回帰を新source boundaryで閉じる。
  204はtotal-expressionのjoin Int∪Intであり、partial converterとの同一視はしない。

### 218 の実source prefixと共有不整合（部分回帰）

- MixedGround218Packet/Frame/Install234: 原source Initialからの実mixed parent install。
  旧installed/final状態のliftではない。非terminal親の新fullInputs/Outputs、全guard、
  非Committed、具体非空Models、実Reachableと版付きGenerated childを証明。
  親の使用する0/1 captureはsingletonなので旧値を保つことを個別に示し、
  未使用名まで全captureが同じだと仮定していない。
- MixedGround218Obstruction234.centers_different: 任意assignmentのparent fullHoldsから
  generated childの二つのactual centerが不同。
- child_input_infeasible: 任意candidateでinput=childSite、head queriesが
  [variables 0, variables 0]、かつ任意installed Models assignmentならHeadSharing.Holdsは不可能。
  candidateのinput/queries条件は明示前提。全current Frameからその条件を導く橋、
  child Fresh/Prepared/SafeKnown/Unique、V8 SharingConflict/rejected、Stable/EvidenceAtは未完。
  条件付き共有不整合を、最終拒否回帰の完成とは呼ばない。

### 有限trusted sliceの合成（一般健全性補助）

SupportUnion234: 任意state・fact列F/G・modelでSliceModels(F++G)は両sliceの連言と同値。
Trusted FかつTrusted GならTrusted(F++G)、有限のtrusted列族のflattenもtrusted。
Readback/ClassReadbackは結合した強いsliceから元sliceへ制限する。
個々のsliceに依存する観測は結合sliceでも正当化できる。循環trustやavailabilityを
仮定・結論に足していない。

## 残る本命の橋

今回の一般橋は既存6本を新kernelへ接続したもの。
残る `progress`, `execution`, `halted`, `whereAccessible`, `treeExecution`,
`canonicalLocalOrder` の6本はまだ未完。

- progressは単なる次stepの存在ではなく、全reachable stateのStepに対するAcc。
  版keyのinjectivityや仮定付き有限候補poolだけでは、endpoint alphabet/長さと
  refresh/reobserve/equate/alias/install全体のwell-founded measureが足りない。
- execution/haltedにはそのAccから実executorを設計し、runのStepsと全kind no-Stepを示す必要。
- whereAccessibleは最終Local selected-childのAcc。個別planのcycle Safeとは同じではない。
- treeExecutionはそのAcc/FrontierExactを使うresolveと実runの辞書の一致。
- canonicalLocalOrderはregistry permutationだけでなく、別runの終点間の分類一致が必要。

この境界のB4Bridgesでは、6 operational項目にEvidenceNode/GeneratedChildrenを加えた
8個のトップレベル項目が未完（M1全体の残件数を数えたものではない）。
一般同時model-extension、非terminalの学習availability/completenessもこれらの内部義務として残る。
有限な二つの実飽和経路を、一般停止性・完全性・主型性の代用にはしない。

## 検証・公開・制限

Lean4.35.0。focused対象指定または新モジュールだけのdirect `lake env lean --trust=0 ... -o ...`。
最初に別worktreeの.lakeが共有リンクであることによるdependency再build競合があり、
Pool231/DiagnosticLaws232のobject欠損を確認。DiagnosticLaws232をdirect再生成し、
以後は新234モジュールだけのdirect compileに統一して解消した。ソースは失われていない。
初期proof/type/timeout失敗は修正し、通った版のみを監査・公開した。

`Audit/Cycle234First.lean`: 18 modules / 209 constants PASS。
`Audit/Cycle234Second.lean`: 22 modules / 292 constants PASS。
`Audit/Cycle234Third.lean`: 8 modules / 76 constants PASS。
`Audit/Cycle234Fourth.lean`: 5 modules / 52 constants PASS。
合計53新modules / 629 constants、全4監査PASS。constantsは定義・recursor等を含み、定理本数ではない。
許可依存はpropext/Classical.choice/Quot.soundのみ。新axiom/sorry/native_decideなし。
最新統合取り込み後、全53新モジュールをdirect trust=0・warningAsErrorで再compileしPASS。
全4監査も最終コードで再実行し、209/292/76/52を再確認。477個のソース宣言位置を索引化した。
全体lake build/verify-lean.shはstanding-ordersどおり実行しない。全体gateは監督側。
途中公開03566227（最初18）、71380edc（40）、4d8c9cc6（48）。最終SHA・remote照合は完了応答で報告する。
使用量枠は不明。publication holdなし。新しい言語意味の判断・質問ノートなし。

### Yulang2との照合

work/dots-auditのx-oracleとrole claimsを再読。
X15/X16は同頭/異頭区間の限られた観測で、版付きjournalやtrusted cacheの実装oracleではない。
今回の表現変更はI44と既存specに基づく内部形式化。新しいYulang2実機実行や一致は主張しない。

## 次の候補（最大3件）

1. 218の実parent install後のchildについて、NameSeparation233.other_root/outside_history等で
   新版leaf keysと親historyの分離を示し、Fresh/Prepared/Unique/SafeKnownとFrame条件を
   繋いで、既証明のchild_input_infeasibleからV8 SharingConflict/rejectedへ閉じる。
2. reachable endpoint alphabet/長さの上限と実版key領域から一般progress/Accを組み、
   executorのexecution/haltedへ接続する。有限例のno-Stepを一般橋と混同しない。
3. 非terminal selectedの全journal/packet/effect同時モデル構成とGeneratedChildrenを証明し、
   EvidenceNode、whereAccessible/treeExecution/canonicalLocalOrderを閉じる。

## 最終集計

公開対象は周全体で73ファイル。最後の追加公開は15ファイル。
研究・証明の量化子レビューを約45分まで継続し、全検証は07:15 UTCまでに完了。
最終公開とremote tree照合の正確な完了時刻・SHAは完了応答で報告する。
