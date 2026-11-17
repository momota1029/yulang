# dots cycle233 — 新境界だけの到達・安定・辞書と版付きtrusted層

開始2026-11-17 05:30:05 UTC。研究・主張のレビューを06:15まで継続（約45分）、その後最終検証・公開。期限06:25:05。
早着した05:28から開始時刻までは待機し、勝手な作業の前倒しはしなかった。
開始時integration6437ed3b、I44とstanding-ordersに変更/STOPなし。
232の報告・completed心拍・公開2411b399と手元tree一致を確認。
競合プロセス/未公開の前周成果なし。今回復旧は不要。
06:07にintegration bc61dca4968d8a544561e9f406dbc04db475c7a5を再取得。standing-orders/inboxは変更なし、I44継続、STOPなし。監督側のPool231コメント修正だけを取り込み、既存意味コードは変更しなかった。
Audit.lean/README.md凍結を維持。barrel末尾追記のみ。
言語意味の新判断や質問ノートなし。旧230反証はそのまま保持。

## 中心結果

232では「旧境界の到達prefixの後に、新境界の1step」までだった。
今回は原source初期化から、**新Kernel232だけの3step**を構成した:

1. 緩い取り込みの版で実install（初版lo=O、hi=W）。
2. 原sourceから正当化したpoint reobserve。
3. point取り込みの別版で実install（新版lo=hi=W）。

両installは全Installable guardと非Committedを満たす。旧/新どちらの
aggregate等式も同じjournalに残る。新しい名前だけを使ったモデルを構成し、
原source・actual中心は保持。終点は**実Reachable、全Kernel Stable、実selected、
非空Models、literal source EvidenceAt、さらに全Modelsに対する辞書evidence**を満たす。

主要パッケージ:
`GeneralDictionaryVersionedRegression233.positive_regression`。
旧230の6slot終点をそのままliftした結果ではない。同じ原5slot source/root/outputを
新境界だけで処理した回帰であり、不要な旧upper refreshは経由しない。

### Stableの範囲は重要

これは現行Kernel232、すなわち**既存legacy trusted cacheを使うkernel**でのStable。
新only source traceではlegacy core.plans/effectsは空のまま。
新aggregateに関するfull journalの意味を、そのまま旧trusted cacheに昇格させてはいない。
source-supported Cutを使い、現在Unknownな任意identityをKnownにする旧Refreshを排除した。

後半で新しいversioned/mixed trusted観測層も構成したが、**kernelにはまだ差し替えていない**。
新cacheをruleへ採用した後にはStable・停止性・回帰を再検証する必要がある。
さらに新版upperをUnknownからKnownにする具体的な新Refresh証明書を構成し、同じcontextへの旧Refresh証明書は存在しないことを証明した。これは補助層の証明書であり、未定義の新kernel Stepや新kernelでの非Stableを主張するものではない。

## 宣言と量化子（位置一覧はverificationのdeclaration-index）

### 新only初期化と最初のinstall

- InitialModel233: 初版2名の割当、原source/旧packet supportの保存。
- InitialPacket233: 具体extendedモデルでversioned full Holds、HeadModels、source保存。
- InitialFrame233: 原sourceのinitial、Prepared/Frame/Unique、実Effect/install、非空Models。
- InitialStep233: 全guardを検証。別モデルで新packetの非充足を示し¬Committedを証明。
  `step`と`reachable`は新SourceBoundaryの実1stepで、旧到達prefixの仮定はない。
- Reobserve233: 任意mixed stateについて、source=snapshotかつcurrent=looseExtended
  （allocated/reserved/ordinaryは任意）なら、実改善reobserve Step、全assignmentのModels iff、
  source・plans/effects・sites保存。
- PointStage233: 初回installedへの具体適用。point snapshot、非空モデル、初版plan/effect保持。

### 同じjournal内の旧/新版と第2install

- Point233: 任意allocated/reserved/ordinaryと任意modelについて、point context Modelsと
  source0=FooWW、source2=W、actual=W、output4=O、新lo/hi=Wという6値条件から
  new packet full Holds/HeadModels、capture/binder/schema/childrenを証明。
- PointFrame233: 上のモデルとfresh名のrawsources外性、context同一、singleton sitesから
  Prepared/Unique/Frame/Ready/ClassEffects/Evidenceを構成。
- PointFresh233: 実pointstage rawsourcesは0..4と初版lo/hiだけ。任意purposeの新版名が外部。
- PointSafety233: 実pointstateのacyclicity、SafeKnown、positions、alternatives、choice。
- BothModel233/BothPacket233/BothStage233: 旧/新4aggregateが同時に正しいモデルを構成し、
  初回fullpacket・初回installed Models・point Models・次のfullpacketをすべて保持。
- InitialTransport233: 任意modelで旧packet Holdsと新旧lo/hi値一致があれば初版new Holds。
  明示条件付き補題であり、全到達状態で値一致するという主張ではない。
- Variant233: 次版2名に任意Tyを代入しても初版installed/point Modelsを保持。
- SecondInstall233: 実Effect/install、旧/新版planの共存、非空Models、全Models evidence。
- SecondStep233: Variant(O)を使って次版¬Committedを証明。実全guard installと
  初期→install→reobserve→installの3step `path`、source `reachable_nonempty`。

### selected・全Stable・非空EvidenceAt

- InstalledEvidence233: 任意state/effectでsnapshot一致・terminal children=[]なら、
  installed Modelsの各modelからreplayed current Frame/Certificate/Evidence。
  旧certificateやEvidence結論を仮定せず、記録済plan/effectとLiveを読む。
- InstalledEvidenceAt233: terminalかつ旧edges空・rawsites全root・実selectedの下で
  literal EvidenceAtを包装。Stableを要しない強いevidence結論を使う。
- PointInstalledSelected233/SecondSelected233: 実終点のSafeKnown、current unique、
  モデルからoutput/sharing/merged conflictsを排除し、実source selectedとEvidenceAt。
- PointEvidenceAt233: 任意pointplan installについて、外側selected/SafeKnown/非空仮定を除去。
  EvidenceAt内部のselectedのUniqueと各validモデルで得るcurrentUniqueを比較する。
  実非空・実selectedは別のSecondSelected/Regressionで確認済み。
- SecondRaw233: 任意終点raw Modelsから初版/新版Ordinaryを回収。
  初lo≃source4、初hi/新lo/新hi≃source2をrawの等式だけから導出。
- SecondEquality233: 9sourceを4意味クラスに分類。任意source対で全journalモデルの
  等式が成立すればRawEqualが既に成立。具体非空モデルで異なるクラスを排除。
- SecondRefresh233: 任意context/identityの旧Refresh証明書で、旧Unknown→新Knownは不可能。
  source membership仮定も不要。Cutは新journal Modelsではなくsource-supported slice。
- SecondStable233: enqueue、refresh、reobserve、equate、install、mergeを全て排除。
  `stable`/`halted`はinstall-only closureではない。
- Regression233: checked、実source Reachable、全Stable、selected、literal EvidenceAt、
  非空Models＋Evidenceを一つにまとめる。全generated子も安定。

### 一般sourceidentity・単調性・registry

- Growth233: 任意Administrative/At/Step/Stepsでsource context、current seed、constructors、
  interpretation保持。新plans/effects、sites/edges、requests、Generatedが単調。
  SourceBoundary Reachableから実initial/source context同一とseed一致を導出。
- Registry233: 任意new-kernel到達でpacket/plan/effectのregistry由来を保持。
  異なるcompiled registryから同じstateへ到達したならpackets空。
  source-initial newReachableのlegacy plans/effectsは空。任意lift legacyへは主張しない。

### 新しいtrusted/readbackの橋（補助層、kernel未変更）

- Support233: Discharged/PacketSettledは記録済**versioned planのchildren**を再帰使用。
  旧Packet.childrenを読み替えず、正確なHead readbackとClassReadbackを残す。
  任意Trustedとfull ModelsからSliceModels、出力factは必ずsettledであることを証明。
- Trusted233: 実終点でTrusted [.output effect,.input plan]を構成。
  任意input sliceモデルで新lo/hi≃W。旧source-only Cut modelLowは新input sliceではない。
  したがって新層は形式だけでなく具体的に強い観測根拠を持つ。
- Observations233: 新trusted sliceに基づくCacheSound/Cut、fullModelsに対する観測soundness。
- ObservationTransport233: 新Refresh/Reobserve証明書から、既存の具体state transformerの
  **全journal Models iff**。基礎制約とcacheを別々に要求し、Models iff自体は仮定しない。
- SupportGrowth233: Monotoneからversioned settlement/Trusted/Readback/Cutを輸送。
  Step/Stepsのcache保存は**同じsnapshot**について。
- SupportCache233: 実installと新観測証明書については、結果のcurrent snapshot cacheも保存。
- MixedObservations233: 独立にtrustedな旧factsと新factsの双方から観測を導くjoint interface。
  旧cache/newcache両方を埋め込み、fullModels soundnessとRefresh/Reobserve iffを証明。
- MixedCache233: joint cacheのgrowth・install・新観測証明書のcurrent cache保存。
- NameSeparation233: 任意aggregate名の衝突はroot/declaration/purpose/name/順序つき端点列の
  全一致と同値。過去の所有/版が異なる有限historyの名前を上書きしない。
  一般到達traceの有限version上限はまだ仮定なしには導いていない。

### 具体的な新版upperの学習可能性

- UpperBase233/UpperSnapshot233: 原5slotを保った6slot拡張。slot5は旧版hiではなく新版hi。seed/ordinary/reserved/allocatedを保持。
- UpperRefresh233: 実終点と具体extendedContextについて新Refresh `certificate`、upper_supported/upper_unknown/upper_known、同じcontextの旧証明書を排除する `no_legacy_certificate`。
- 任意modelについてrefresh前後のfull Models iff (`model_preserved`)。新cacheの具体的な追加能力を示すがkernel232は未変更。

### 新source境界での追加回帰

- Conflict199233/Conflict199Local233: 実source初期化、非空モデル、Prepared/FrameからOutputConflictによる拒否、全Stable、literal EvidenceAt。ただしselectedが排除されるためEvidenceAtはこの拒否例では空虚。
- Default202233/Default202Local233: 実source初期化、非空モデル、全Modelsのdefault packet/certificate/evidence、実selected、全Stable、literal EvidenceAt。
- Join204233/Join204Local233: join Int∪Intについて同様の新source回帰。total-expressionのjoinでありpartial converterではない。
- Gap206233/Gap206Safety233/Gap206Install233: 実source初期から全guard付き新installとReachable、Intモデル保持、bottomモデル除去、全installed Modelsでdefault Evidence。postinstalled Stable・selected・literal EvidenceAtは未証明。

## 受け入れ条件と残件

I44の原230 source例について、新境界だけの実到達・実Stable・selected・非空EvidenceAtを達成。
source identity/単調性の一般保存も閉じた。12橋のうち既存6橋を維持したが、
一般progress、execution、halted、whereAccessible、treeExecution、canonicalLocalOrderは未完。
一般有限version pool、停止性、executor、無条件EvidenceNodeを完了とは呼ばない。

199/202/204は上記範囲で完了。206はinstall後のStable・selected・EvidenceAtが残り、218の新境界回帰は未着手。
新trusted層のsoundnessと具体利用は閉じたが、kernel採用・legacy/new trust相互依存の完全性、
非terminalでの学習availability/progress、一般EvidenceNodeは残る。
新しいexact反例は見つけていない。旧230反証の主張や証明を弱めていない。

## 検証と公開

Lean4.35.0。新モジュールをfocused `lake build Yulang.<module> --wfail`で検証。
最新integration取り込み後、51新targetsを明示したfocused再buildもPASS（依存込み1534 jobs、全体barrel buildではない）。
全体lake build/verify-lean.shはstanding-ordersに従い実施しない。全体gateは監督側。
独立 `lake env lean --trust=0 Audit/Cycle233*.lean`:
- First: 20 modules / 251 constants PASS。
- Second: 9 modules / 139 constants PASS。
- Third: 8 modules / 203 constants PASS。
- Fourth: 6 modules / 86 constants PASS。
- Final: 8 modules / 142 constants PASS。
- 合計: 51新modules / 821 constants、全5監査PASS。最新integration取り込み後にも5監査をすべて再実行しPASS（final-reaudit.txt）。

constantsは定義・生成recursor等を含み、定理本数とは呼ばない。
許可依存はpropext/Classical.choice/Quot.sound。新axiom/sorry/native_decideなし。
初期syntax/type/lint失敗は修正し、通った版だけを監査・公開した。
ログ全文と宣言位置一覧はnotes/verification/cycle233/。
途中公開7086d54a（最初20）、f260d9f1（29）、15bcc1e3（37）。最終公開は残り14modules・報告・検証ログを含む。最終SHAと照合結果は完了応答で報告する。
使用量枠は不明。環境中断やpublication holdはなし。

## 次の3件

1. 新/mixed trusted観測interfaceを実kernelへ接続し、具体回帰のStable・cache不変量を再確認。
   今周のlegacy-cache no_refreshをそのまま新cacheに流用しない。
2. 一般selected/current frameに対する同時model-extensionを閉じる。
   新名と全旧history supportの分離、再訪版の既存等式、actual/子/関連出力の整合性を同時に扱う。
3. reachable endpoint alphabet/length boundから有限version poolを導き、残る6橋・停止性・
   executor/EvidenceNodeと残りの回帰を閉じる。一般の進捗仮定を具体回帰と取り違えない。

最終検証完了06:16 UTC、開始から約46分。公開・remote tree照合の所要時間は完了応答で報告する。

公開対象は周全体で75ファイル（51新Lean modules、5監査、barrel・報告・design・索引・ログ・心拍、および監督由来のPool231コメント修正）。最終追加公開は28ファイル。
