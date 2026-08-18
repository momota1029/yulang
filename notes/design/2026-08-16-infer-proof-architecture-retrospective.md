# infer proof architecture retrospective と次世代設計原則

日付: 2026-08-16

状態: **ユーザ承認済み（2026-08-16）。retrospective・分析文書として承認。実装 authority ではない**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定。

注記: ユーザが当初想起していたのは「クリーンなYulangを1から作る場合の設計そのもの」（重視点・高速化を最初から組み込むか後付けするか）を扱う文書であり、本書はそれとは別に価値を認められ承認された。ゼロベース設計の文書は後継作業として別途起草する（§9の未決定事項1・2・10を引き継ぐ）。

## 0. 本書の目的

repositoryのperformance-crisis session全体は約6週間に及ぶ。そのうち本書が詳細に再構成する
2026-07-31から2026-08-16までの直近17日間だけでも、`infer` crateのconstraint solving / proof verification
subsystemではcorrectness redesignとperformance crisisが連鎖した。個々の設計は、その時点で観測できた根因に対して
必要だった。しかし全体を通して見ると、同じ関係を複数の物理表現へ展開し、それらを同期・再検証するコストが、
一つ前の修正後に次のbottleneckとして露出する形が繰り返されている。

本書は、個々の設計を失敗として一括評価する文書ではない。各設計が何を解き、何を意図的に残し、その残りが
後続事件とどう結びついたかを再構成する。その上で、次のどちらにも使える設計原則を第一稿として提示する。

1. 現行世代の`infer`をsubsystem単位でretrofitする。
2. yulang1から現在の世代へ移ったときと同じ規模感で、次の世代のYulangを設計する。

本書は後者を既定結論にしない。逆に、直近のfirefightingを単なる局所実装ミスとして片づけ、現行architectureを
無条件に延命する結論にも立たない。

### 0.1 本書における「次のYulang」の解釈

ユーザの発言にある「Yulang2」は、literalなcrate名や既存codebase名を指すとは解釈しない。
repository historyでは、2026-06-08に新しい`sources` / `infer` / `poly` routeを旧pipelineから分離する薄い入口として
`yulang2` crateが追加され、その後`yulang2` frontを中心にrewriteが進んだ。commit `e7aea138`のmessageも
「spec-driven sources/infer/poly rewrite with yulang2 as the entry point」と記録している。現在の`crates/yulang`にも
「Yulang2 language server」というruntime textが残る。

従って本書は、ユーザの「Yulang2」を、**現在の世代の名前を再利用する提案ではなく、yulang1から当時のyulang2へ
移ったときのような、もう一度のgeneration-scale redesign / ground-up successor**という意味に読む。この解釈自体も
未承認であり、ユーザが別の意味を意図していた場合は査読時に修正する。

### 0.2 「外部proof system」の作業定義

本書でいう外部proof systemとは、proof kernelの外部serviceを指さない。productionのcanonical decisionとは別に、
legacy store、shadow store、migration adapter、exact parity oracle、trace oracle、test fixture authorityが、同じsemantic
relationをもう一度構築・照合し始め、実質的に**第二のproof implementation**となった状態を指す。

この第二系統はmigration中には必要になり得る。問題は存在そのものではなく、次が未定義のまま恒久化することである。

- 何を正本とし、何をderived viewとするか。
- どのeventで、どのdeltaだけを同期するか。
- 全量照合一回のcostと、suite全体のcost上限はいくつか。
- いつ、どのgateで、誰がshadow / oracle / legacy writerを削除するか。
- parity対象がsemantic resultなのか、canonical orderなのか、historical traceなのか。

## 1. 調査範囲と証拠の扱い

### 1.1 読んだ正本・履歴

本書は少なくとも次を直接照合した。

- `CLAUDE.md`のdesign historyとperformance incident記録。
- `notes/design/2026-07-31-claim-parent-delta-materialization.md`（CDM）。
- `notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md`（MPC）。
- `notes/design/2026-08-01-derived-unary-premise-nodes.md`と
  `notes/design/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md`（DPN）。
- `notes/design/2026-08-01-urr-v3-causal-qualification.md`（URR-v3）。
- `notes/design/2026-08-02-mpc-dpn-projection-evaluation-round.md`。
- `notes/design/2026-08-02-replay-claim-parent-factorization.md`、
  `notes/design/2026-08-02-rcpf-quarantine-retry-authority-addendum.md`、
  `notes/design/2026-08-03-rcpf-d-materialization-projection-addendum.md`。
- `notes/design/2026-08-07-cpk-8-legacy-removal-plan.md`、
  `notes/design/2026-08-07-cpk-8g-physical-removal-plan.md`、
  `notes/design/2026-08-07-cpk-8g-4b-cycle-cut-parity-addendum.md`。
- `notes/design/2026-08-10-generalized-witness-claim-bridge-provenance-gap.md`（GWCB）。
- `notes/design/2026-08-11-projection-clause-link-factorization.md`（PCLF）。
- `notes/design/2026-08-12-qualified-parent-replay-occurrence-factorization.md`（QORF）。
- `notes/design/2026-08-12-cpk-preflight-structural-validity-addendum.md`、
  `notes/design/2026-08-13-cpk-sv-c-dynamic-dependency-synchronization-addendum.md`、
  `notes/design/2026-08-13-cpk-sv-d-sealed-conservative-cache-plan.md`、
  `notes/design/2026-08-14-cpk-sv-d-ss2-read-foundation-resequencing-addendum.md`。
- 2026-08-16のcommits `c98a36ee`、`3223043c`、`f33c2158`。
- forward-looking assessmentの置き場所のprecedentである
  `notes/design/2026-07-02-parting-assessment.md`。

### 1.2 数字の証拠強度

正本文書またはcommit messageに残るcensus / wall / RSSは、そのartifactの数字として引用する。異なるmachine、build mode、
revisionの数字を一つの連続benchmarkのようには扱わない。

今日のlegacy-oracle修正について、repositoryに残る強い証拠は次である。

- commit `4463af53`は、`cprov_a_characterizes_constraints_replay_std_and_regressions`単体が約41分で、
  45分CI timeoutの主要因だったと記録する。
- `c98a36ee`のdiffは、PCLF-A、QORF-B、QORF-D0の三full reconstruction oracleがordinary writer commit
  pathから毎回呼ばれ、formula / result-local growthをquadraticにしていたと明記する。
- `3223043c`は1〜16 commitをdense、以後power-of-twoと1024 commitごとに再検証するcheckpointへ変えた。
- `f33c2158`は、checkpoint間で生じて直るdivergenceだけでなく、unsampled commitで壊れたrecordが二度と
  revisitedされない場合も検出できないと、残余coverage gapを明記する。

ユーザがこのsessionで観測した80〜1200倍のsuite slowdown / speedup rangeは重要な一次観測だが、指定された三commitには
per-test before/after表として保存されていない。本稿では**owner-reported session measurement**として扱い、正本承認前に
command、revision、build mode、median、RSSをbenchmark artifactへ固定することをopen itemとする。

また、本稿調査中に現HEADで上記`cprov_a`を180秒timeoutで再実行したが完了しなかった。これは41分時点より改善していないという
証明ではないが、「三oracleのcheckpoint化によりinfer suite全体のperformance crisisが解消済み」とも言えない。

## 2. 実際に起きたこと

### 2.1 2026-07-31: MPC — flat ORからproof clause ownershipへ

MPCの主題はperformanceではなくsoundnessだった。projection changeのproofをflatなORとして扱うと、mixed proofが
「どれか一つのparentが成立すればよい」と誤読される。そこで`Standalone`、`DerivedUnary`、`ReplayConjunction`からなる
clause DAGへ変え、一回のtraversalでmemoする設計になった。

この時点で重要なのは、consumerが要求するproofの**論理cardinality**が増えたことである。後のPCLFが示すように、
logical exact clause-linkは真正なoccurrenceであり、単純なsemantic dedupで消してよい重複ではなかった。MPCは後続の物理膨張を
作るための誤設計だったのではなく、必要な意味論を導入した。ただし、その意味論をどのnormalized relationで保持し、複数consumerへ
どう投影するかは、この時点では独立したarchitecture contractになっていなかった。

### 2.2 2026-07-31: CDM — appendごとの全parent再走査

commit `95b95586`がexact-carrier dedup keyを修正すると、`std::text::parse` module loweringは6.126秒から
481.875秒へ悪化した。dedup修正が新しい意味論バグを作ったのではない。隠れていたclaim-parent insertion pathが、
新しいexact parentを一件追加するたびに既存parent全体を再走査し、eager projectionを再materializeしていた。

CDMは「今回追加された差分だけを処理する」台帳とindexへ変え、文書の実装結果では481.875秒から46.930秒へ改善した。
bulk再計算はtest-only equivalence oracleへ退役した。

CDMは初期仮説へ半分だけ一致する。直接の根因は同じrelationの複数copyではなく、**materialized viewの更新単位がdeltaでなく
full prefixだったこと**である。一方、CDM §5.3はoccurrenceとparent summaryの完全分離をblast radiusのため明示的に延期した。
RCPFは二日後、その延期された物理表現そのものを扱うことになる。

### 2.3 2026-08-01: DPN / root-cycle addendum — proof node一般化と必要なindex

DPNは`DerivedUnary` premiseをRecord、Constraint、RootCoverageへ一般化し、map missを偶然のfallbackでなく構造的な
proof stateとして扱った。root/cycle addendumでは、arena ID順をcausal orderとみなせないためtri-color cycle guardを導入し、
`root_claim_by_producer_constraint`をcommon writerからだけ更新するappend-only indexとして追加した。

これは重要な反例である。**derived indexが存在すること自体は今回の根因ではない**。DPN indexには単一owner、限定された
identity、明確なreaderがある。問題なのは、同じcurrent factを複数writerがauthorityとして所有すること、またはconsumerごとに
full payloadを再materializeすることである。

### 2.4 2026-08-01: URR-v3 — motivating fixtureと原因局所化の失敗

URR-v3はcausal qualificationを導入しようとしたが、pinned controlをovermatchし、代替pathも成立しなかった。さらに、
motivationとなったbugはhand-built LVB witness自体がinvalidだったと判明し、propagation変更はdiscardされた。

これはphysical non-normalization episodeではない。ここから得る原則は、large redesign前にmotivating fixture、layer、
reachable production pathを検証することである。共通patternへ無理に含めるべきではない。

### 2.5 2026-08-02: MPC/DPN evaluation round — 同一snapshotの再計算

CDM後、DPN/MPC経路は別のperformance regressionを露出した。約1530万query、link attemptの約70%がexact duplicate、
evaluator queryにも約780万件のduplicateが観測された。caller側の局所skipだけでは300秒timeoutを解消できず、
snapshot/view単位のround memoとnatural-event batchが必要になった。

これも物理copyそのものより、**同じcompleted viewをconsumer境界ごとに再評価するreconciliation cost**の問題である。
今日のoracle事件と同じく、「同じ入力なら同じ答えになる」ことを全eventで再証明するcost modelが無かった。

### 2.6 2026-08-02〜03: RCPF — carrierごとのparent-set full copy

RCPFのcensusは決定的だった。

| 指標 | 実測 |
|---|---:|
| claim-parent総数 | 50,416,990 |
| replay claim-parent | 50,386,734 |
| exact clause-link | 28,524,776 |
| unique qualified carrier | 878,089 |
| parent membership / carrier | 57.4167 |

semantic clauseのduplicateが多いという仮説は反証された。exact clause 847,758、semantic clause 844,415で差は
約0.4%にすぎず、`ReplayConjunction`ではexactとsemanticが一致した。実際の根因は、同じendpoint parent-setを
各exact carrierへfull copyするjoinのphysical non-normalizationだった。

RCPFはoccurrence、immutable shared parent-set、consumer summaryへfactorizeした。この時点でCDM §5.3の延期を回収した。
しかしmigrationはshadow ledger、dual-write oracle、evaluator cutover、materialization cutover、link cutover、legacy removalを
必要とした。quarantine/retry addendumはFactoredとLegacyRollbackのattempt authorityを分離し、D addendumはresult-local index、
commit phase、publication fenceを設計した。つまり「正規化する」だけでは済まず、既に存在するconsumerとtransaction orderingの
全てが移行costになった。

さらに、RCPF-D完了時の`std::text::parse`は48.705秒baselineから53.239秒へ約9.31%悪化した。新しいfactored pathを
追加してもlegacy physical facesが残る間はbenefitが出ないことが実測された。RCPF-Eではwriter boundaryで失われるprovenance、
pre-event view、mixed fixture authorityが見つかり、RCPF-F着手時には事前censusが見落としていたflat storeのproduction consumerが
五つ見つかった。

warning signは文書内にもあった。full expansionはoracle/debug/exportに限る、shadow期間にmemoryが危険ならsampled oracleまたは
短いfixtureへ切り替える、とRCPF自身が定めている。しかし「migration完了後、どのCI pathから、何日以内にoracleを外すか」は
repository-wide lifecycle contractとして固定されなかった。

### 2.7 2026-08-05〜08: CPKとCPK-8G — authority cutover後のphysical removal

CPKはproof decision authorityを新しいstoreへ移したが、authority cutoverだけでは旧storageは消えなかった。CPK-8/8Gのcensusでは、
27のflat proof-only `TypeBounds` field、五つのRCPF store、legacy reader/writer、adapter、oracle、telemetryが残った。
CPK-8Gは17 slice規模でownership transferとphysical deletionを行い、explicit Legacy authorityを直接構築するtestは51件、
routing holdoutを含むauthority/oracle依存は54件に達していた。

これは独立した第六のfactorizationではなく、RCPF/CPK migrationの**未払いphysical removal cost**を可視化したepisodeである。
「new authorityが正しい」と「old representationが消えた」は別のmilestoneであり、後者を完了条件に入れなければ、memory、writer、
test、review surfaceは残り続ける。

cycle-cut parity addendumは別の問題も示した。cross-authority oracleがcycle cut countまで一致させていたが、先行設計はshort-circuitにより
cut countが異なり得ると認めていた。最終semantic decision / payloadではなく、incidental traceをoracleにしたため、canonical CPK orderを
採用し、cut-count parityを削除する必要が生じた。

### 2.8 2026-08-10: GWCB — provenance transportのcardinality契約

GWCBではproof storeにexact replay bridgeが存在したが、projection/generalization transportがroot/representativeへ縮退し、
decisive clause identityを失っていた。rev.1の「trueなOR armを全て運ぶ」案は、round evidence cacheで200.154秒 / 15.57 GiB、
baseline 176.341秒 / 約8.8 GiBを外れ、persistent true-arm indexも240秒超 / 15.58 GiBとなった。

rev.2はcacheを増やすのではなく、evaluatorが既に行うshort-circuitのcanonical-first decisive arm一件をcaptureするsemantic contractへ
変更した。最終値は170.87〜176.19秒、RSS 9.33 GiBだった。

GWCBは「canonical representationが無かった」episodeではない。正本のproof relationはあった。問題はconsumer transportが必要とする
cardinalityを決めないまま、all-arm materializationを正しさの保険として選んだことだった。従って次世代原則にはstorage normalization
だけでなく、**各queryが返すproof certificateの最大cardinality**が必要になる。

### 2.9 2026-08-11: PCLF — clause bodyをlinkごとにfull copy

PCLFのcensusではlogical exact linkが28,526,006件、distinct clauseが847,858件で、平均33.6448 link/clauseだった。
各linkにfull clause bodyを格納していたため、occurrenceの97.0278%が同じclauseの二個目以降の物理copyだった。これはsemantic
duplicateではなく、bipartite relationの一方のnode payloadをedgeごとに埋め込んだdenormalizationである。

attempt 70,610,294件のうち42,084,288件、59.6008%はno-state-change duplicate/re-touchだったが、caller/writer recheckだけを
除いてもwallは動かなかった。主因はpayload duplicationとread topologyだった。

PCLFはformula entry、support group、compact incidence、canonical nonempty runへfactorizeした。しかし正しいreader実装三案は、
nested iterator topologyとlocalityのため10.9〜20.6%遅くなった。rev.3でexplicit cursor、canonical run、chunked AVLを設計し、
最終的にparse 77.9秒付近から68.571秒、full 127.97秒から121.96秒、RSS 9.33 GiBから7.812 GiBへ改善した。

ここから、normalized storageだけを設計しても不十分だと分かる。**read traversalのshape、nonempty skip、cursor state、cache localityまでが
physical designの一部**である。

### 2.10 2026-08-12: QORF — 既存occurrence relationの二重・三重保持

QORFではqualified replay entry 50,390,357件と既存CPK replay finite-map parent 50,390,357件がfull tupleまで完全一致し、
mismatchはzeroだった。つまり「似たrelation」ではなく、同一relationを別consumerのために再保持していた。

qualified storeは28-byte keyのglobal hashとresult-local 28-byte canonical vectorを持ち、約3.322 GiBを占めた。既存occurrence ledgerを
authorityへ昇格し、side chunk membership、occurrence arm、root winner、streaming association cursorへfactorizeすることで、
約3.266 GiBをgross saving対象にした。non-replay structural/reduction-routeは30,256件だけで、小さなflat storeへ残した。

correctness cutover直後はlocality悪化によりparse +3.27%、full +2.81%となり、legacy retirementまで性能判断を延期した。
QORF-Eでduplicate physical facesを削除した後、parse medianは68.571秒から56.787秒（-17.185%）、fullは121.96秒から
90.857秒（-25.503%）、RSSは7.812 GiBから約4.296 GiB（-45%）へ改善した。

QORFは初期仮説を最も強く支持する。同一logical factに複数の物理authority/viewがあり、削除までbenefitが現れなかった。

### 2.11 2026-08-12〜14: CPK-SV — validationの反復とdynamic leaf shadow

CPK-SVのRMW N=6では`validate_record`が50,266,205回呼ばれ、79.274%がalready checked、20.600%がactive cycle revisit、
genuine expansionは0.126%だった。premise observationはunique premiseに対して784.58倍、95.615%のclauseと99.873%のpremiseが
同一serialで再観測されていた。cross-serial rescanは八record、14 clauseにすぎず、epoch deltaが主因という仮説は反証された。
同じcompleted snapshotを異なるroundが何度も検証することが根因だった。

CPK-SV-Cの初案はcurrent claim/live valueをformula-owned validation actionへcopyしようとした。その結果、formula writerがdynamic
authorityのcurrent valueを知り、dynamic writerがformula dependentsを知って全copyを更新する相互fanoutが必要になった。さらに
stale prepareをsilent `()`で捨てた後もcallerがprepared accepted entriesをpublishし、mandatory proof relationが欠落するbugが見つかった。

redesignはformulaにstable obligationだけを持たせ、claim/live current valueはquery時に各single authorityからlate-bindした。
これは本書のroot hypothesisを直接支持する。ただし解は「indexを全て消す」ではなく、stable relationはformula、dynamic current factは
claim/live authority、joinはquery snapshotというownership分離だった。

CPK-SV-Dはさらに、cache-relevant mutationをsealed gatewayのsingle finalizerへ閉じ、snapshot invalidationを一つのwriterへ集約する
設計となった。そこへ至るまで、writer census、aggregate counter、site counter、sealed gateway単独、conservative default単独など
六roundが不成立になった。これはphysical relation duplicationと同一ではないが、subsystem-wide authority closureを後付けで証明する
costが非常に高いことを示す。文書自身の見積りは5,000〜10,000 semantic lines、9,000〜18,000 visible diff、少なくとも9 sliceである。

### 2.12 2026-08-15: row 1 terminal gate — 同じ事件ではなく、crisis発見の直前文脈

row 1 witness/compaction migrationは四案連続で`NOT SOUND`となった。`CompactRoot::default()`がneutralなunknownではなく、実際には
`Never` / `Any`という強いsemantic valueになるため、failure時fallbackとして公開できなかった。第五案はattempt-local poisonと
checked lowering boundary、hover/completion/member completionの三post-format terminal gateを分離し、最終的に承認された。

これはrelation denormalization事件ではない。ここでの教訓は、internal recovery valueとuser-visible output authorityを分け、
terminal stateをfinal output boundaryで一度だけgateすることである。今日のoracle問題は、この大きなmigration後にCIを通そうとした
過程で発見された別件である。

### 2.13 2026-08-16: PCLF/QORF legacy parity oracle — migration safety netの恒久hot-path化

PCLF/QORF migration中に追加された三つのdebug oracleが残っていた。

1. PCLF-A read modelをlegacyからfull reconstructionするoracle。
2. QORF-B side shadowをlegacy side全体のsortで比較するoracle。
3. QORF-D0 result-local legacy projectionをfull rebuildするoracle。

いずれも`#[cfg(test)]`だったが、ordinary writer commitごとに呼ばれていた。test workloadが成長するほど、増え続けるprefix / resultを
毎回再構築するためquadraticになる。release costがzeroでも、CIとlocal debug feedback loopにとってはzero-costではなかった。

`c98a36ee`はいったんこれらをdedicated parity testへ限定した。`3223043c`はmigration coverageをordinary real writerにも残すため、
commit 1〜16、power-of-two、1024ごとのcheckpointへ戻し、transient corruption regressionを追加した。`f33c2158`はsamplingが
検出できない二種類のgapを明記した。

これはRCPF文書が二週間前に既に予見した「full expansion oracleは限定し、危険ならsampleする」を、migration完了後のtest lifecycleへ
適用できなかったepisodeである。また、checkpoint頻度はboundedでも、各checkpointのfull reconstruction sizeは増えるため、suite全体の
漸近costが自動的にlinearになったわけではない。現HEADの`cprov_a`が本稿調査でも180秒以内に完了しなかった事実を含め、oracle修正を
infer performance問題全体の完了宣言には使えない。

## 3. 共通patternの判定

### 3.1 初期仮説はどこまで正しかったか

初期仮説「claim / parent / formula / occurrence relationにsingle canonical representationが無く、新consumerやmigration oracleが
shadow copyを作り、同期・検証costが次のbottleneckになる」は、方向として正しい。しかし、そのままでは二点粗い。

第一に、局所的なcanonical storeは存在した。RCPFにもclaim identity、PCLFにもexact membership authority、QORFにもCPK finite-map、
GWCBにもexact bridgeがあった。問題は「canonicalが一つも無い」ことではなく、**logical fact family全体について、authority、derived
view、join、consumer、lifecycleを閉じるsubsystem-wide contractが無かったこと**である。

第二に、五つの代表事件はmechanismが完全には同じでない。

| episode | 主な物理問題 | 初期仮説への適合 |
|---|---|---|
| CDM | appendごとのfull-prefix view再計算 | 部分一致。copy数より更新単位の問題 |
| RCPF | endpoint parent-setをcarrierごとにcopy | 強く一致 |
| PCLF | clause bodyをexact linkごとにcopy | 強く一致 |
| QORF | 同一qualified relationを複数storeに保持 | 最も強く一致 |
| 2026-08-16 oracle | legacy viewをwriterごとにfull reconstruction | 広義で一致。persistent data copyよりrecomputed shadowの問題 |

従って正確な共通項は、**derived relationまたはequivalence proofを、bounded delta / bounded query / bounded lifecycleなしに物理化する**
ことである。物理化はpersistent `HashMap` / `Vec`だけでなく、commitごとのfull rebuild、全arm transport、same-snapshot revalidationも含む。

### 3.2 繰り返されたloop

実際のloopは次だった。

1. correctness / provenance consumerが、新しいexact relationまたはcertificateを必要とする。
2. 最短の安全策として、既存relationのconsumer-specific flat copy、reverse map、full payload edge、legacy-equivalence shadowを作る。
3. migration中の安全のため、old/new両方をwriteし、full parityをevent境界で検証する。
4. correctness gateは通るが、logical件数、physical件数、amplification、revalidation回数のbudgetは完了条件にならない。
5. authority cutover後もold writer/store/oracle/test fixtureが残る。新consumerは到達しやすいfaceを読む。
6. workloadが数千万edgeへ成長し、またはtestがfull stdを通ると、memory / wall / CI timeoutとして初めて観測される。
7. emergency censusでcardinalityを測り、factorization、delta、memo、late binding、samplingを後付けする。
8. correctness cutover時点ではnew+old両方が動くため一時的に遅くなり、physical removalを別projectとして行う。
9. 一層外側のconsumer / projection / oracleに同じshapeが残り、次のcrisisになる。

RCPF、PCLF、QORFが連続した理由は、同じconceptual proof graphを別のedge familyごとに局所最適化したからである。一つのrelationを
factorizeしても、その上のqualified admissionやprojection linkがfull payloadを持つなら、amplificationは一層外へ移る。

### 3.3 共通のarchitectural root cause

本稿のworking diagnosisは次である。

> `infer` proof subsystemには、logical fact familyごとのsingle authority、normalized identity、derived-view definition、
> incremental maintenance rule、query cardinality、reader topology、migration lifecycleを一体で所有する層が無い。
> そのため新consumerは独自の物理viewを作り、migration verifierは独自のsecond implementationを作る。
> correctnessは局所oracleで守れるが、同期面と検証面の総costを誰も所有しない。

これは単なる「premature optimization不足」ではない。むしろ反対で、正しさを守るための局所的な冗長性が、system-wideな
cost modelなしに積み上がった結果である。必要なのは、後からhotspotを速くする技法より、**冗長表現を作るときにauthorityと
削除責任を同時に負わせるarchitecture**である。

### 3.4 事前に見えていたwarning sign

危機まで完全に不可視だったわけではない。

- CDMはoccurrence/summary分離を明示的にdeferしていた。
- CDM自身がbulk pathをtest-only oracleへ退役させた。full reconstructionのtest costを別budgetとして追わなかった。
- RCPFはfull expansionをoracle/debug/export限定とし、memory危険時のsamplingまで文書化していた。
- RCPF-Dはlegacy physical faceを消すまで速くならず、実際に9.31%悪化した。
- RCPF-E/Fではwriter-boundary provenanceと未発見consumerが後から見つかった。狭いcall-site censusではauthority closureを証明できなかった。
- CPK-8Gはauthority cutover後も54のauthority/oracle依存testと多数のstoreが残ることを数えた。
- PCLFは正しいfactorized readerでも20%級に遅くなり、storage schemaだけでなくread topologyが必要だと示した。
- QORFはlegacy relationとCPK relationの件数・tupleが完全一致していた。新しいconsumer storeを作る時点でcross-store identity censusを
  必須にしていれば、3 GiB超の重複は早期に見えた可能性が高い。
- CPK-SV-Cはoptional dynamic leaf shadowを明示的に棄却し、「shadowでも二重ownerの同期code、reverse map、capacity、review surfaceを
  残す」と書いている。
- `CLAUDE.md`は重いfull-std suiteをskipしないと8時間超・30 GiB級になり得ると警告していた。これは運用上必要だった一方、
  slow testを日常pathから避けることがroot costの発見を遅らせる面もあった。
- 2026-08-16直前のCI修正はtimeoutを45分から90分へ上げた。stopgapであることはcommit messageに明記されたが、
  timeout拡大が一時的にroot causeを隠す構造だった。

warningは存在したが、それらを一つのarchitecture smellとして集計するownerとgateが無かった。

### 3.5 同じpatternへ含めないもの

本稿は次を同じ原因へ強制的に畳まない。

- MPCとDPNのproof node追加は、必要な意味論の表現であり、単なるtest bloatではない。
- DPN root indexはsingle writerの必要なderived indexである。
- URR-v3はinvalid fixtureと原因局所化の問題である。
- GWCBはcanonical store不在よりcertificate cardinality contractの問題である。
- CPK-SV-Dの六round failureはwriter exhaustivenessをRust typeだけで証明できない問題である。
- row 1 terminal gateはfailure containment / output authorityの問題である。

ただし、これらは共通root causeの周辺条件を補う。semantic relationのcardinality、mutation authority、failure boundary、fixture validityを
別々に設計しなければ、normalized storeだけ作っても次世代architectureは成立しない。

## 4. 次世代またはfundamental retrofitで最初から採る原則

以下は一般論の標語ではなく、上の事件から逆算したcontractである。

### P1. Logical factごとにsingle authorityを宣言する

各fact familyは、設計時に次を一行で答えられなければならない。

- identity keyは何か。
- current value / append-only occurrence / historical provenanceのどれか。
- authoritative writerはどのtransactionか。
- authoritative readerはどのquery interfaceか。
- 他のmap / vector / certificateはauthorityかderived viewか。

「同じtupleを別名のstoreでも持つ」は禁止しないが、二つを同格authorityにはしない。QORFのようにfull tuple parityがzero mismatchなら、
新storeを作る前に既存authorityのviewで表現できない理由を文書化する。

### P2. Logical identityとphysical layoutを分離する

`claim × parent × carrier × side × result`のようなlogical relationを、consumer structのfield layoutで定義しない。stable IDとnormalized
relation schemaを先に定め、flat view、ordered cursor、portable export、diagnostic sequenceはその上のprojectionとする。

これによりPCLFのclause body、RCPFのparent-set、QORFのqualified tupleをedgeごとに埋め込むdefaultを避ける。exact semanticsを
preserveすることと、exact payloadを全edgeへcopyすることを分離する。

### P3. Derived viewにはowner、delta、invalidation、retirementを必須fieldとして持たせる

derived viewを追加するdesignには、最低限次の表を置く。

| 項目 | 必須内容 |
|---|---|
| source authority | どのfactから導出するか |
| owner | 誰だけが更新するか |
| update unit | event-local delta / batch / snapshot rebuildのどれか |
| invalidation | source mutationとの対応 |
| readers | 全production/test consumer |
| physical budget | entry、bytes、amplification上限 |
| removal | permanentなら理由、temporaryなら削除gateと期限 |

この表をproof relation registryとしてrepositoryに保ち、code censusと同期させる。fieldを増やすだけのinventoryではなく、
authority graphをreview可能にする。

### P4. Appendはdeltaで処理し、full-prefix reconciliationをevent pathへ置かない

CDMをdefaultにする。新fact一件のadmission costは、そのfactが新たに作るincidenceとaffected consumer deltaに比例させる。
既存prefix全体のscan、sort、rebuildは、明示されたbatch boundaryかoffline verifierにしか置かない。

どうしてもfull rebuildが必要なviewは、commitごとでなくversioned snapshotへbindし、同snapshotで一度だけ計算する。MPC/DPNと
CPK-SVのsame-snapshot repeatをarchitecture levelで禁止する。

### P5. Dynamic factはstable obligationからlate-bindする

CPK-SV-Cを一般化する。formula側にcurrent claim locationやlive stateをcopyしない。formulaは
`(representative, expected_root)`のようなstable obligationを持ち、query snapshotでclaim/live authorityへjoinする。

snapshot IDはcache validityに使ってよいが、複数writer間のownership reconciliationやsemantic conflictの代用にしない。

### P6. Query / certificateの最大cardinalityを設計する

GWCBのall-arm失敗を繰り返さない。各queryは「全proofを返す」「decisive proof一件を返す」「summaryを返す」「streamする」のどれかを
明示し、worst-case output cardinalityを持つ。正しさの保険として全arm / 全parent / 全traceを返す案は、callerが本当に必要とする
semantic contractを先に証明してから選ぶ。

### P7. Read topologyをstorage designと同時に決める

factorization後のiterator nesting、empty bucket skip、cursor resume、ordering、chunk localityを後回しにしない。PCLFのように正しい
normalized representationでもreaderが20%遅くなり得る。

design gateには、point lookup、ordered traversal、result-local traversal、full exportの各complexityとallocationを含める。
「expected O(1) mapがある」だけでhot-path costを説明したことにしない。

### P8. Mutationはtyped prepare/commit/receiptを通し、secondary publicationはreceiptだけを見る

CPK-SV-C/Dの教訓を採る。callerがprepared candidateを見てsecondary relationをpublishしてはならない。authoritative commitが
`Changed` / `Unchanged` / conflict / failureをtyped receiptで返し、receiptに含まれるcommitted deltaだけを後続consumerへ流す。

cache-relevant mutationはsingle finalizerを通す。scattered writer末尾の手書きsnapshot bumpや、early returnが迂回できるepilogueを
authorityにしない。

### P9. Migrationはphysical removalまでを一つのdefinition of doneにする

new read authority cutover、old writer停止、old reader停止、old store削除、adapter削除、oracle削除、legacy fixture retirement、
wall/RSS再測定を一つのmigration manifestに置く。

dual-writeを開始するcommitには、同時に次を必須にする。

- owner。
- expiry condition。
- maximum supported workload / RSS。
- production defaultで到達する期間。
- deletion PR/slice。
- rollback artifactの保存方法。

「後でCPK-8Gを行う」をnormal processにしない。physical removalが同じprojectの終端である。

### P10. Oracleは正しさcontractとperformance budgetを同時に持つ

legacy-equivalence oracleを追加するとき、次のtierを最初から選ぶ。

1. 小fixtureのevery-mutation exhaustive oracle。
2. targeted medium fixtureのevent-boundary exhaustive oracle。
3. broad suiteのsampled checkpoint。
4. env-gated / scheduled full-workload end-state oracle。
5. migration完了後に残すdirect semantic contract test。

各tierに最大wall、最大RSS、最大reconstruction件数、CI frequency、retirement gateを置く。`#[cfg(test)]`は性能免除ではない。

samplingはcoverage tradeoffを明記する。`3223043c`型のglobal commit samplingはreinspection intervalをrecordごとに保証せず、
full reconstruction sizeもboundedにしない。必要ならpartitioned rotating sample、deterministic hash sample、changed-record sample、
end-state full comparisonを組み合わせる。

### P11. Oracleはsemantic contractを比較し、incidental traceを正本にしない

CPK-8G cycle-cut countのように、short-circuitで変わり得る内部traceをexact parity対象にしない。比較対象を次へ分類する。

- exact semantic identity。
- canonical consumer-visible order。
- diagnostic provenance。
- performance counter。
- implementation trace。

最後の二つは通常correctness authorityではない。historical insertion permutation、cycle cut count、iterator visit countを固定する場合は、
user-visible semanticsである理由を別途示す。

### P12. Testをcontract / migration / characterization / benchmarkへ分離する

legacy authorityを直接構築するtestを、new authorityへ機械的に書き換えて温存しない。

- contract test: 現在のsemantic invariantを固定し、恒久的に残す。
- migration parity test: old/new equivalenceだけを検証し、migration終了時に削除する。
- characterization: historical gapや未決定behaviorを記録し、正本ではないことを示す。
- benchmark/scaling: outputでなくcost envelopeを固定する。

各testにclassとownerを持たせ、migration parity testが通常suiteへ残ったらcensusで失敗させる。

### P13. Logical / physical / recomputedの三つを常時計測する

後からtemporary instrumentationを入れない。proof subsystemは少なくとも次を通常telemetryまたはcheap censusとして持つ。

- logical facts / exact incidences。
- distinct node payloads。
- physical entries / bytes。
- accepted / duplicate / re-touch attempt。
- full rebuild件数とscan element総数。
- same-snapshot cache hit / miss / repeat。
- max、p95、平均fanout。
- logical-to-physical amplification ratio。

RCPFの57.4167、PCLFの33.6448、QORFのexact parity、CPK-SVの784.58倍が、crisis後でなく最初のscaling gateで見えるようにする。

### P14. Scaling lawをcorrectness invariantと同格にする

small green testだけではquadratic pathを検出できない。代表的なsynthetic familyについてN、2N、4Nを測り、accepted fact数とwall / visit /
allocationの増加率をgateする。fixture名やabsolute timeだけでなく、work unit ratioを使う。

最低限、次のaxisを分離する。

- carrier数を増やしparent-setを固定。
- parent数を増やしcarrierを固定。
- clause数を固定しlink数を増やす。
- result数を固定しqualified parentを増やす。
- snapshotを固定しquery round数を増やす。
- mutation数を増やしoracle checkpoint costを測る。

### P15. Motivating fixtureとproduction reachabilityをredesign前に検証する

URR-v3の教訓をprocessへ固定する。large semantic changeの前に、fixtureがvalidか、production routeから到達するか、症状のlayerと
root causeのlayerが一致するかを独立に確認する。counterexampleがinvalidなら、general ruleを追加してtestを通さない。

### P16. Performance budgetをreview authorityにする

correctness reviewが`SOUND`でも、performance contract未計測ならlanding完了ではない。逆に、一時的なdual-write期間のregressionは
許容できるが、その場合もdeadline、peak RSS、rollback条件を明記する。

timeout延長やheavy-suite skipは運用stopgapとして記録し、root fixのtaskを自動的に閉じない。

## 5. 次世代proof coreの最小architecture sketch

これは実装指示ではなく、上の原則をcode shapeへ落とせるかを議論するための叩き台である。

### 5.1 Fact authority layer

claim、parent、formula、occurrence、qualification、projection supportをstable IDとnormalized relationとして所有する。各relationは
append-onlyかmutable-currentかを型で区別する。raw consumer structはrelation payloadをownしない。

### 5.2 Commit and delta layer

solver mutationはattempt-local batchとしてprepareし、commit receiptがnew / removed / changed fact IDを返す。derived view maintainerは
receiptのdeltaだけを受ける。full-store observerをwriter callbackへ登録できないようにする。

### 5.3 Arrangement / view layer

consumer-specificなkey order、result-local index、side membership、canonical sequenceはnamed arrangementとして宣言する。
各arrangementにsource relation、maintenance rule、memory budget、readerを持たせる。

ここでsemi-naive / differential dataflow型の考え方は有力だが、特定libraryやDatalog採用を本稿では決めない。重要なのは、
「N個のphysical viewを手書きで同期する」ことをdefault solutionにしないことである。

### 5.4 Snapshot query layer

queryはcompleted snapshotへbindし、同snapshotのsuccessful resultを再利用する。dynamic factはlate-bindする。query resultは
owned certificateまたはscope-bound cursorで、cardinality contractを持つ。raw store referenceをconsumerへ返さない。

### 5.5 Verification layer

production kernelと独立なreference verifierを持つ場合でも、常時全量dual executionにはしない。小fixture exhaustive、broad sample、
scheduled end-state full compareに分け、budget超過で自動失敗する。migration終了後はreference verifierをoffline conformance toolへ移すか、
targeted testだけへ縮退する。

### 5.6 Cost observability layer

各relationとviewはlogical entry、physical byte、delta work、query workを自己計測する。benchmark reportはcorrectness oracleと同じartifactへ
保存し、設計reviewがcardinality assumptionを確認できるようにする。

## 6. Successor、retrofit、hybridのtradeoff

### 6.1 Ground-up successor

#### 利点

- authority registry、normalized relation、delta receipt、bounded oracleを最初から中心に置ける。
- 現行`proof/mod.rs`とscattered ownerのcompatibility制約から離れられる。
- performance scaling lawをpublic architecture contractにできる。
- current subsystemで後付け困難だったprivacy、transaction、snapshot boundaryを小さいkernelから始められる。

#### cost / risk

- 現行proof semanticsはMPC、DPN、RCPF、CPK、GWCB、PCLF、QORFを通して獲得した大量のsubtle contractを持つ。rewriteはそれらを
  再発見するriskが高い。
- diagnostic provenance、canonical order、cycle behavior、failure precedence、portable proofを同時に再現する必要がある。
- old/newを長期間dual-runすると、まさに本稿が問題視する「外部proof system」を最大規模で再作成する。
- language全体のrewriteに広げると、infer architectureの改善がparser、lowering、runtime migrationに埋もれる。
- clean designでもrepresentative workloadを通すまでcardinality assumptionは検証できない。

従ってsuccessorは、greenfieldだから自動的に速くなる選択ではない。最初からbenchmark constitutionとshadow expiryを持たなければ、
現行と同じloopをより大きなscaleで繰り返す。

### 6.2 現行architectureのretrofit

#### 利点

- QORF-Eの-25.5% full wall / -45% RSS、PCLF、CDMの改善は、現行codeでもfactorizationが実利を出せる証拠である。
- 現行semantic corpus、diagnostic、portable proof、regressionを直接利用できる。
- relation familyごとにphysical removalまで完了し、benefitを逐次回収できる。
- language front / runtimeを巻き込まず、root causeに近い範囲へ投資できる。

#### cost / risk

- RCPF/CPK-8Gが示すように、一つのauthority migrationが十数sliceと多数consumerの移行になる。
- hidden reader/writerとtest-only authorityが後から見つかる。
- CPK-SV-Dの見積りどおり、ownership sealingだけでも9,000〜18,000 visible diffになり得る。
- compatibility期間のdual storageがperformance budgetを圧迫する。
- subsystem-wide relation registryを後付けしても、既存型がconsumer ownershipを前提にしている部分は残る。

retrofitは「rewriteより安全で安い」とは限らない。既存semanticsを保持できる代わりに、migration coordination costを払う。

### 6.3 Hybrid: architecture successorをvertical sliceで置換する

本稿時点で最も検証可能なのは、language全体の一括rewriteでも、局所patchの継続でもなく、次の中間案である。

1. 次世代proof coreのauthority/view/cost contractをgreenfieldのdesign + small executable modelとして先に作る。
2. 一つのbounded relation familyをpilotにし、現行front/loweringからtyped deltaを渡す。
3. old/new full dual-runではなく、small exhaustive + deterministic sampled + end-state verifierで比較する。
4. pilotがsemantic parityとscaling gateを満たしたら、old physical faceを同じproject内で削除する。
5. 二つ以上の異なるrelation familyで同じcore abstractionが成立してから、successor scopeを拡大する。

これは「successor in architecture, staged replacement in repository」である。最終的にnew crate / new generationになる可能性も、
現行`infer`内部のfundamental refactorとして収束する可能性も残す。

hybridにも危険がある。boundary adapterが恒久化すれば新旧二重architectureになる。従ってpilot開始前に、成功時のold path削除と、
失敗時のnew path全削除を同時に設計する必要がある。

### 6.4 現時点のhonest assessment

約6週間のsession、特に本書が再構成した直近17日間のreactive firefightingは、ground-up impulseを十分に正当化する警告である。
同じsubsystemで、同じfamilyのcost failureが
少なくとも五回現れたことを「偶然の実装ミス」で片づけるべきではない。

一方、この履歴だけでlanguage全体のrewriteを決める証拠もまだ無い。CDM、PCLF、QORFは現行architecture上で大きな改善を実現し、
CPK-SV-Cはsingle authority + late bindingへ正しく修正できた。問題が`infer` proof coreへ局在するなら、language generation全体でなく
proof coreの世代交代で足りる可能性がある。

従って本稿はfull rewriteをrecommendationとして確定しない。まずarchitecture inventoryとpilotで、次を測るべきである。

- 現行に残るlogical-to-physical amplificationの総量。
- relation authorityを閉じるのに必要なconsumer migration数。
- normalized delta coreを現行APIへ接続するadapter cost。
- representative workloadでのscaling law。
- parity oracleをbudget内に収めたままsemantic confidenceを得られるか。

この結果で、retrofitのcoordination costがsuccessorのsemantic recreation costを上回るかを判断する。

## 7. 次のdecision package

本稿承認後も、直ちにimplementationへ入らない。次の小さなdecision packageを作る。

1. **Proof relation registry census**: current store / identity / writer / reader / physical count / derived status / oracle / removal stateを一覧化。
2. **Performance constitution**: representative workloads、N/2N/4N scaling、wall/RSS、amplification、CI oracle budgetを固定。
3. **Pilot候補比較**: append-only occurrence、dynamic current fact、ordered projectionの三種類から一つ選ぶ。
4. **Success / stop rule**: semantic parity、physical removal、cost envelopeを満たす条件と、new pathを撤去する条件を先に決める。
5. **Naming / repository boundary**: new crate、`infer` child module、external modelのどこに置くかを、pilot scopeが決まってから決める。

このpackageは新しい大規模shadow implementationを作る前に、read-only censusとsmall modelで反証可能にする。

## 8. 本書の置き場所

本書は`notes/design/2026-08-16-infer-proof-architecture-retrospective.md`に置く。

理由は次である。

- `notes/design/2026-07-02-parting-assessment.md`が、通常のimplementation instructionではないforward-looking assessmentを
  `notes/design/`に置くprecedentになっている。
- 本書もsigned design historyを横断し、将来のarchitecture decisionへ長期参照される。
- `notes/progress/`は日次事実、`tasks/`は実行queueであり、本書の役割と違う。
- 一文書のために`notes/retrospectives/`等の新taxonomyを作ると、既存のdesign historyから発見しにくくなる。

ただし場所が`notes/design/`でも、本稿はauthorityではない。top-level statusをdraft/unapprovedとし、Claude reviewとユーザ承認を
経るまでimplementation decisionの優先順位へ入れない。

## 9. 未決定事項

1. ユーザの「Yulang2」が本稿のgeneration-scale redesign解釈で正しいか。
2. 対象をlanguage全体、`infer` crate全体、proof coreだけのどこまでにするか。
3. normalized relation coreをhand-written Rust、relational engine、semi-naive evaluator、別のmodelのどれで実現するか。
4. persistent provenanceとon-demand reconstructionの境界をどこに置くか。
5. diagnostic / portable proofが必要とするcanonical orderをどこまでauthorityに含めるか。
6. broad sampled oracleの許容coverage gapと、scheduled exhaustive oracleのfrequency。
7. migration shadowの最大存続期間をcalendar time、commit count、slice gateのどれで表すか。
8. owner-reported 80〜1200倍の測定を、どのcommand / revision / machineのartifactとして保存するか。
9. 現HEADでも180秒を超えた`cprov_a`に残るcostの内訳と、本稿のpatternに属する割合。
10. pilotをretrofitとして始め、途中でsuccessorへ昇格するdecision gate。

## 10. 第一稿の結論

今回の履歴から得られる最も強い結論は、「もっと早くoptimizeする」ではない。

**proof relationを追加する時点で、semantic authority、physical view、delta maintenance、query cardinality、verification budget、
physical removalを一つのdesign unitとして扱う必要がある。**

RCPF、PCLF、QORFは、同じproof graphの別の層でfull payload copyが連続して見つかった。CDM、MPC/DPN、CPK-SV、今日のoracleは、
persistent copyでなくてもfull-prefix reconstructionやsame-snapshot revalidationが同じcost failureを作ると示した。CPK-8Gは、
authority cutoverだけではdebtが消えず、physical removalとtest retirementが独立projectになることを示した。

従って「single canonical representation」は有用な出発点だが、最終原則としては狭い。必要なのは、single authorityを核に、
必要なderived viewを明示し、bounded deltaとbounded verificationで維持し、temporary shadowを確実に消すarchitectureである。

ground-up successorかretrofitかは、まだ決めない。ただし、同じ形の第六・第七のcrisisを局所factorizationだけで待つことも選ばない。
次の一手は、proof relation registry、performance constitution、bounded pilotによって、どちらのpathが実際に小さいriskでこの原則を
成立させられるかを測ることである。

## 11. 2026-08-16 追記: successor直行の決定によるsupersede

本書の承認後、2026-08-16にユーザは、本書が提案したproof relation registry census、bounded pilot、successor / retrofitの
decision gateという順序を採らず、ground-upなYulang3 successorへ直接進むことを明示的に決定した。repositoryの優先順位では
明示的なユーザ指示が署名・承認済みの先行文書より上位にあるため、この決定により§9の未決定事項2（redesignの対象範囲）と
10（retrofit pilotからsuccessorへ昇格するdecision gate）は解決済みとなる。両項目は、本書が提案したpilot processによってではなく、
ユーザの直接決定によって解決された。

この二つのdecision pointについて、以後のauthoritativeな方向は`docs/yulang3-architecture.md`をsuccessor documentとして扱う。
ただし、本書の13 episodeの履歴、P1〜P16、architecture patternの分析を含む診断内容はsupersedeされない。supersedeされるのは、
successorとretrofitのどちらへ進むかを決めるために§6.4、§7、§9が提案したprocessだけである。

同日、ユーザは、`notes/design/2026-08-04-mutable-reference-performance-investigation.md`に記録され、
`docs/yulang3-architecture.md` §6.9のYulang3側design decisionからも参照される、Yulang2の未解決なMechanism 2
mutable-reference constraint fan-out性能問題をYulang2へbackportして修正しないことも明示的に確認した。これは意図しないfreezeの
副作用ではなく、Yulang2をpatchする代わりに、state-slot designで問題を根本から解くYulang3 Phase 3のreference solverへ工数を
振り向ける、明示的かつ意識的なtradeoffである。そのため、Yulang2のmutable-reference RMWに現在見られるsuperlinearなslowdown
patternはYulang3の初期開発期間を通して残る。この継続は見落としではなく、受容された結果である。
