# dots cycle232 — 実install・guard付きsource boundary・元のEvidenceAt

開始2026-11-17 04:31:12 UTC。研究区切り05:16:12、公開照合期限05:26:12。
I44・standing-ordersを再読。integration6437ed3b1、変更/STOPなし。
231は完了済みで公開treeと一致し、未公開成果/競合プロセスなし。復旧不要。
凍結Audit.lean/README.md不変。言語意味論の新判断・質問ノートなし。

## 今回閉じた中心部分

1. **実際に記録するinstall**。旧journalのplans/effectsは旧意味のまま保持し、
   新しい版付きplan/effectを別listに記録。current contextには新cross/merges/
   selfChecks・予約・所有key、子site/rawsite/edgeを実際に追加する。
2. 任意state/effect/modelについて、snapshot一致の下でinstall後Modelsを
   「旧full Models、新full Holds、snapshot/live effects、全旧/new live effects」
   と厳密に特徴付けた。旧制約や出力条件を捨てていない。
3. 230例の任意旧fullモデルから、全旧journal sourceのAssignment値を保全して
   新installedモデルへ延長できる。新installed Modelsは旧Models+新mergesと同値。
   その全モデルに現行frameの辞書証拠があり、モデル非空を実証した。
4. V8の分類規則は変えず、版付きcandidate、full mixed Modelsによるcycle判定、
   actual-head共有、output conflict、旧/new merged history sliceを接続。
   旧と同じ全guardを備えた実Kernel.Stepと、HeadAlloc encodingを通るsource boundaryを作った。
5. 230の旧到達状態からの**新境界の全guard付き1step**、新状態のV8 selected、
   元の **B4SkeletonV8.EvidenceAt** を証明した。別名で結論を仮定した定理ではない。

## 重要な未完了部分

旧境界のsource-initial Reachable prefix + 新境界1step、という事実をそのまま
報告している。初期から最後まで新境界のStepだけを使うReachableは未証明。
別のmigration-fragmentにはsource-initial pathがあるが、これを新境界の
Reachableと言い換えていない。最終全kernel Stableも未証明。
install-only fragmentでは全current frameをreplayPlanへ一意化し、再install不能を証明した。

Literal EvidenceAtの証明はStableを仮定せず結論を示せるほど強い具体全モデル証拠に
基づく。非空モデルとselectedも別に示しており、空Modelsや選択不成立で閉じていない。
それでも一般EvidenceNode・M1完成・新境界の完全停止性は主張しない。

12橋渡し条件は、stepModels/closure/frontierLocal/localIdentity/
dictionaryRefl/initialReordersの6項を個別に証明。
progress/execution/halted/whereAccessible/treeExecution/canonicalLocalOrder、
さらにGeneratedChildren/一般EvidenceNodeは未完。executorを仮定して完成扱いしない。
199/202/204/206/218の新境界回帰も今周は未完。旧証明・反例は保持。

## 追加Leanと量化された主張

全宣言名の索引: notes/verification/cycle232/declaration-index.txt。
以下の一般補題はroles/state/plan/modelなどを任意とし、書いた条件を明示前提とする。
正確な型・補助宣言は各sourceを参照。

### 記録と実行の土台

- GeneralNominalVersionedJournal232: State/Effect/Models/lift/initial。
  lift_models、initial_modelsで旧意味をそのまま回収。new planのfull Holdsを全記録へ課す。
- GeneralNominalVersionedChildren232: emitted_occurrencesはcanonical順でchildrenと完全一致。
  任意new total Holdsから全child Site.Holds/raw SiteHolds、追加辺からGeneratedを証明。
- GeneralNominalVersionedInstall232: install_models/step_models。任意snapshot一致で上述の
  完全Models iff、旧plans/effects/source保持、新plan/effect/childrenの実記録。
- GeneralNominalVersionedInstallProperties232: 全旧raw/center/edge/packet/Generatedを保持。
  context一致ならsource base/seed/Known保存、new/old key ownership、子Generated。
- GeneralNominalVersionedTerminal232: children=[]ならsites/rawsites/request集合が不変。
  任意旧Modelsの旧live effectsを保持。
- GeneralNominalVersionedInstallStep232: common model・Generated focus・非Committedの下の
  実非冗長install relation。各stepのモデル後退保存、非空性、記録済みplanのCommitted。
  このrelation単独を完全solverとは呼ばない。
- GeneralNominalVersionedCommitted232: install後のreplayPlanも全モデルでCommitted。
  同一観測の再構成だけで無限に再installすることを排除。全trace停止性ではない。
- GeneralNominalVersionedFrameTransport232: 同一contextとsite包含の下でFrameを移送。
  request membership一致の下でReady/ClassEffects等が同値。
- GeneralNominalVersionedReplayEffects232: 任意ordinary extension/replayPlanで、同一core/root/modelの
  Ready/ClassEffects/明示・defaultのOutputWitnessが元planと同値。
- GeneralNominalVersionedFrameFunctional232: 同一registry/core/root、decl/rawsite/centerが
  各singletonなら任意2FrameのPlanは一致。keysも一致。

### 230の実installとmigration

- GeneralDictionaryVersionedInstalled232: 実effect/installedを構成。
  任意mでModels installed m iff旧230 Models mかつ新merges。every_model_extendsで任意旧mを保全。
- GeneralDictionaryVersionedNovel232: 新2aggregateだけをOへ割り当てる旧fullモデルを構成し、
  新current packetを満たさないことからbeforeの非Committedを証明。新target反例ではない。
- GeneralDictionaryVersionedEvidence232: 全installed Modelsに現行Frame/Certificate/Evidence、
  非空性、任意旧モデルの保全延長付きevidence。
- GeneralDictionaryVersionedStep232: 新非冗長install relationの実step。
- GeneralNominalVersionedRefresh232: 旧の構造的/trusted Refresh・Reobserve certificateを前提に、
  mixed Modelsの正確な同値。new plans/effects保持。結論自体をcertificateに仮定していない。
- GeneralNominalVersionedMigration232: 版付き記録がないlegacy prefix、新install、
  certified refresh/reobserveからなる明示的migration relation。steps_models/source_models。
- GeneralDictionaryVersionedReachable232: 元source initialからこのmigration relationで実installedへ到達。
- GeneralDictionaryVersionedInstallClosed232: installedでGenerated需要はrootのみ、
  任意Frameはreplayed、一切のInstallStepがない。全solver Stableではない。

### V8診断と具体安全性

- GeneralNominalVersionedCycles232: 全mixed Models上のEqual/Head/Edge/Path/Cyclic、Root/Candidate cycle。
  raw CandidateK2の旧HeadReadyだけをversioned Preparedへ整合移植。その他raw条件は保持。
- GeneralNominalVersionedAcyclic232: 実Models証人と全sourceの明示有限Form条件の下でrank下降→¬Cyclic。
- GeneralDictionaryVersionedAcyclic232 / RawAcyclic232: installedの実モデルを与え、
  全originのsemantic cycleと全6slotのraw recurrenceを排除。旧raw辺の流用ではない。
- GeneralNominalVersionedHeadSharing232: 新head SchemaHolds/full Holdsから
  既存HeadSharing220.Holds（同名actual originsの等式）を導く。endpoint等式へ弱めていない。
- GeneralNominalVersionedMergedConflict232: 新plan/effectを全て含むhistory/class slice。
  legacy liftでは旧MergedOutputConflictと同値、全Models/class equationsによるconflict排除。
- GeneralNominalVersionedDiagnostic232 / DiagnosticLaws232: local-only V8 fieldsと
  local_total/local_functional。明示safe/unique/実full model/Frame/Holds/ClassEffects/非mergedの下でselected。
  この診断用boundaryのfalse Initial/Stepを完成したoperational boundaryと呼ばない。
- GeneralDictionaryVersionedSelectionFacts232 / Selected232: installedのPrepared/Unique []/
  AdministrativeReady/Known/SafeKnown、実モデルによるoutput/sharing/merged conflict排除、V8 selected。

### Guarded境界と既存橋渡し

- GeneralNominalVersionedAdministrative232: 実enqueue/equate/merge。
  enqueue/equateのModels後退保存、merge_modelsは追加atomsと全旧/new live条件を含む厳密iff。
- GeneralNominalVersionedKernel232: 全enqueue/equate/refresh/reobserve/install/merge rule。
  元guard（cache/materialized/choice/positions/alternatives/common/novelty等）を保持。
  step_models/steps_models/closureを任意step/pathで証明。
- GeneralNominalVersionedBoundary232: 本物のInitial/Kernel.Step/Stableを備えるraw-registry V8 boundary。
  診断Localとの同値、stepModels/closure/initialReorders/dictionaryRefl。
- GeneralNominalVersionedSourceBoundary232: 既存HeadAlloc registry encodingを通すsource-facing wrapper。
  checked/initial/reachable compiled、Local/EvidenceAt同値と同じ4橋。
- GeneralNominalVersionedFrontiers232 / SourceFrontiers232: 任意checked registryで
  frontierLocal/localIdentity。停止executorや子木accessibleはまだない。
- GeneralNominalVersionedRecorded232: 全実Kernel操作でeffect→記録plan不変条件を保持。
  実boundary ReachableとModelsから、各newEffectにfull newHoldsがある。
  任意手構築Stateについては主張しない。
- GeneralDictionaryVersionedGuarded232: beforeのSafeKnown、trusted cache、完全materialization、
  choice、cycle/全alternatives、common、noveltyを個別に証明し、全guard付きKernel.Stepを構成。
- GeneralDictionaryVersionedEvidenceAt232 / GuardedRegression232 / SourceRegression232:
  literal EvidenceAtとselected・非空全モデルevidenceを実source boundaryへ接続。
  到達prefixが旧境界であることを型にも明記。

### 観測cacheの追加作業

- GeneralNominalVersionedCache232: 具体TrustedGrowth/Recorded transportにより
  versioned install後も既存legacy CacheSoundが保たれる。
  新effectをtrusted根拠として使う完全性は未証明。
- GeneralNominalVersionedKernelCache232: 全Admin/At/Stepと実Reachableに対する既存cache保存。
- GeneralNominalVersionedSourceInvariants232: source encoding境界のReachableへRecorded/full Holds/cache不変量を輸送。

## 検証・公開

各moduleをLean4.35.0 focused lake build Yulang.<module> --wfailで検証。
全体lake build/verify-lean.shはstanding-ordersに従い未実施。全体gateは監督側の仕事。

独立 lake env lean --trust=0:
- Audit/Cycle232First.lean: 13 modules / 190 constants PASS。
- Audit/Cycle232Second.lean: 26 modules / 275 constants PASS。
- Audit/Cycle232Final.lean: 3 modules / 15 constants PASS。
- 合計: 42 modules / 480 constants PASS。
constantsには定義・生成補助宣言を含む。新定理の個数とは呼ばない。
許可依存はpropext/Classical.choice/Quot.soundのみ。sorry/新axiom/native_decideなし。

途中公開: 1fd95450（13modules）、b821d2f2（39modules/465constants時点）。
最終追加分・報告・ログ・心拍も手元に留めず公開する。
初期の局所syntax/type/patternエラーは修正し、成功した版だけを監査・公開。
環境中断/承認待ちなし。使用量枠は不明。

## 次の3件

1. 新境界だけのsource-initial traceと全kernel Stableを230で閉じる。
2. newEffectのsettled/readback条件を保ったtrusted observation factsを接続し、progressのcache availabilityを示す。
3. 実traceでの有限version pool/整礎測度と残る6橋、GeneratedChildren/EvidenceNode、
   199/202/204/206/218回帰を閉じる。

詳細: notes/design/2026-11-17-cycle232-remaining-bridges.md。

## 最終レビューで明記した境界

legacy PacketSettled/Dischargedは旧Packet.childrenを読み、新installの実edges/sitesは版付きchildrenを使う。既存Trusted保存はこの一致を主張しない。非terminal settlementや新trusted事実の導出にはversioned settled/readback、または新旧children対応証明が必要。これは新反例ではなく未完の表現境界である。

## 最終チェックポイント

05:16 UTCに研究を区切り、全42対象のfocused build成功（1484 jobs、依存を含む）。
最終監査15を合わせ480宣言の監査成功。各監査ログ・宣言位置一覧・focused buildログを
notes/verification/cycle232/に収録。凍結2ファイルはintegrationと同一、diff --check成功。
公開は既存work/dots-main HEADを親に、期待SHA付き更新で行う。最終SHAは最終返信で報告。
