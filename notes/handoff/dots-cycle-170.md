# dots cycle170 — 局所coverageからの有界辞書構築とnamed spineの残る穴

開始2026-11-13 17:26:17 UTC（定期run17:27:19 UTC）。ユーザーの55分上限を優先し、保守的な終了期限を18:21 UTCとする。最初にintegration/m1-finalと常設指示・inboxを取得し直し、前169のcompleted心拍と公開報告を読んだ。前169のworker・compileは終了、並行writerなし。

## 復元と公開

初回integration `9ab07935f083cde5c1ff986d034f853449dc0a55`。初回心拍・integration統合は `9c0f01b2f53ad4dfa6da36b37ba587a6cc80dcc1`。17:44再取得で `898526b04164829e196293fee0128e756d41e208` に進んだため新しいAstra ground-readback群を統合した。inboxはI27まで同じACTIVE、STOP・最大サイクル上限なし。

GitHubアプリでwork/dots-mainだけをexpected_sha付き更新。最初の6module・36定理のsourceは `a4cfe3b588e883b7d707211427c5a204b68ae99a`、tree `b99c12704978999748b72d308c2922e7d973689c`。中間10module・61定理のsourceは `9e1febb08784db6030756319bea1e3a682e65ddc`、tree `7fefa86935b186e99ff9b0d6746c439d2e4b0985`。それぞれローカル凍結treeと一致を確認してからrefを進めた。spec、notes/plan、Astraの既存定義、lake設定、凍結Audit.lean/READMEは変更していない。Yulang.leanはimport追加のみ。

## 成果の要点

**11新module・69公開定理。すべて補助または健全性補助であり、完全性・主型性の完成ではない。**

1. recorded/scalar/spine/scalar-namedの四種類の局所NodeからCoverageを定義した。子辞書やEvidenceをNodeに含めない。固定journalの最大親IDによるrankから、任意のchild-closed domainでAccを導く。有限domain・Acc・モデルを追加仮定せず、Coverage存在そのものはまだ外部義務。
2. **実際に計算する辞書assembler**を定義した。fuel=0ならnone、正fuelなら実child順序で再帰してnodeを構築。任意の成功結果はNamedTreeであり、rank+1 fuelで必ず成功する。SourceFormedなら、その一つの計算済みpayloadが全現在モデルでEvidenceを持つ。Coverageを任意プログラムから発見するアルゴリズムではない。
3. ordinary traceで局所Coverageのkey・子順序・domainを保存し、**buildのOption結果そのものが一致**する。状態ごとのrank上限が異なっても、成功した異なるfuelのpayload一意性を用いる。任意descriptor refreshは扱わない。
4. 一つの辞書経路のedge数はrank以下。さらに固定journalの実最大子数Bから、成功出力の全node数をcap(B,fuel)以下と導く。cap(B,0)=0、cap(B,n+1)=1+B*cap(B,n)。重複部分木も数える。言語実行やLean実行時間・メモリの上界ではない。
5. 実現在モデルを明示して、構造的named leaf/treeとLocal.selectedのkey・順序つき子一覧を照合。terminal payloadの一意性を示す。全モデルEvidenceだけからモデル存在を推論していない。
6. **新しいnominal-input/named-output実例**を作った。三つの入力binderを持つternary nominal入力と非空named nominal出力を、実source観察から解釈する一般NamedSpine.Shapeを証明。モデルとInitialSourceも存在する。scalar入力の既存例を再命名したものではない。後半の追加で実Shared Stableも示した。零stepのterminal初期例であり、新しい非ゼロstep実行ではない。
7. 同じ新実例には、今回の四種類の局所Nodeが存在しないことも証明した。空journal、旧leafのoutputs=[]、scalar-namedのinputNames=[]にそれぞれ矛盾する。**局所証明書がまだ狭いという穴**であり、Evidenceは実際に存在する。V5の反例ではない。

## 13境界とV5

| 境界 | 状態 |
|---|---|
| Checked | 一般nominal定義を維持、新nominal実例で成立 |
| Models | 一般定義を維持、全現在モデルと実例の明示モデルを区別 |
| Step | Shared/ActualInspection定義を変更せず。ordinaryは実関係の制限 |
| Stable | 一般定義を維持。新spine初期実例の実Shared Stableを追加検証 |
| Generated | 一般定義を維持。生成から局所coverageの一般導出は未完 |
| RootPending | 一般定義あり、変更なし |
| RootK2 | 一般定義あり、変更なし |
| CandidateK2 | 一般定義あり、変更なし |
| InspectionPending | 一般nominal定義あり、全Shared境界の統合は未完 |
| Survivor | 一般定義あり、変更なし |
| Evidence | 構造的局所構築、計算assembler、named spine解釈を追加 |
| Reorders | 一般定義あり、変更なし |
| DictionaryEquivalent | 一般定義あり、変更なし |

V5は**未証明8/14**のまま。全Shared evidenceNode、Reachable/StableからのCoverage存在、適切なguard/Installable、完全性・主型性・全言語coverageは閉じていない。I26のguardは弱めず、保留consumerへ辞書を与えたとは主張しない。今回のsemantic Evidenceは、ReadyAtだけから得た結論ではない。

## 検証

- Lean4.35.0、`lake build Yulang.GeneralDictionary170… --wfail`（10moduleを個別列挙）: PASS、790jobs。全repo buildは重い過去障害のため実行していない。
- 各新auditを `lean -j1 --trust=0` で実行: PASS。中間all-declaration gateは10moduleの**275宣言**（生成宣言・privateも含む）を検査し、許可公理propext/Classical.choice/Quot.soundのみ。
- 初回公開exact SHAを別worktreeに取得し、6moduleの既存oleanを排除した別libraryへすべて再コンパイル。全7audit PASS、159宣言gate PASS。依存cacheは再利用しており全repoのfresh buildではない。
- `tools/verify-lean.sh . 898526b04164829e196293fee0128e756d41e208 --no-build`: PASS（diffのみ）。5 REVIEWは新規読取auditのrun_cmd。production宣言を生成するメタプログラムはない。
- 統合したAstra群も `lake build Yulang.GeneralNominalSourceProjection Yulang.GeneralNominalGroundReachable Yulang.GeneralNominalGroundPacketForest Yulang.GeneralNominalClosedPatternMass Yulang.GeneralPatternRecordSubstitution Yulang.GeneralNominalRecordInversion --wfail`: PASS、746jobs。これを今回の61定理には加算しない。
- 独立read-only reviewで全10moduleの量化、同一現在モデル、rank/fuel、実計算、全node数とruntimeの区別、新実例とcoverage gapの位置づけを確認、問題なし。

最終公開exact SHAの独立replay結果は下の終了台帳に追記する。sourceのmanifestと全定理型・公理ログはnotes/verification/cycle170-*へ保存する。

## 失敗・修正・制限

- 初期のLean elaborationでOption bindの簡約、依存型のroot分解、queryのDecidable未装備に遭遇。明示型・一般化したnode除去・構造的simpへ直し、成功後だけ公開した。sorry/axiom/native_decideは使わない。
- 作業開始時に別workerへ同じworktreeの別新規pathを渡したが、git-concurrency規則の再確認後すぐ独立worktreeへ移した。以後のworker書込み・再検証は別worktree/library。既存source競合や消失はない。
- integration統合でYulang.leanとdesign INDEXが競合。最初のunion処理が追加importを落としたが、公開前append-only/import gateで検出し、全importと既存separatorを復元。修正後PASS、既公開Leanから削除行0を確認した。
- tree候補がローカルcommitと一度不一致になった。原因は最終auditの完了ログがcommit時には空だったこと。完了した275宣言ログをcommitし直すと完全一致した。不一致のref更新は行っていない。
- generic uniform Evidenceはモデル存在を含まない。named scalar fixtureとnew named spine fixtureだけ明示モデルがある。Coverage選択にclassical choiceが使われる場合があり、assembler自体は供給済みCoverageに対する計算。
- token使用量・利用枠は不明。

## Yulang2との照合

work/dots-auditを再取得、`55574b6052ef1534fd0fc36d6d3617ebede59a0e` のnotes/audit/x-oracle.mdを再読。X1のDisplay where実使用と、旧runtimeが新specと違うX2を確認した。今回のnominal入力/named出力の構造的Lean辞書と旧runtimeの一般同値は未証明。新しい実機実行はしていない。旧runtime挙動を仕様へ逆輸入しない。

## 次の義務

1. NamedSpineの局所constructorを含む拡張coverageを構成し、新実例の証明済みの穴を埋める。そのうえでReachable/Stableからcoverageそのものを導く。CoverageをV5へ新仮定追加して解決扱いにしない。
2. actual snapshotのrequest観察とpacket relocationを、一般descriptor refreshで保存する。ordinaryの一致を任意Stepへ拡張したと呼ばない。
3. 最新AstraのReachableCaptureFactorization/semantic readbackと、source-slot付き有限観察証明書を接続する。source Patternの再構成だけでは現在snapshotのnominals/headsは得られない。

## 公開69定理の量化台帳

以下は実例と明記しない限り、roles・registry・state・context・domain・需要・宣言・payload・fuelを任意に量化する。各auditの`#check`が完全な型を保存する。分類「補助」はV5完全性/主型性の達成ではない。

### NamedCoverage（4）
- `node_tree`【補助】: 一つの局所Nodeと、実順序childrenに対応するAll₂ NamedTreeから、同じkeyを持つ親NamedTreeを構築。
- `accessible_tree`【補助】: Coverageとdomain内root、その選択子関係のAccから有限NamedTreeを構築。
- `wellFounded_tree`【補助】: 同じ結論を選択子関係のWellFoundedから導く。
- `uniform_dictionary`【健全性補助】: Coverage・Acc・Shared SourceFormedから、一つのpayloadとNamedTree、および全現在モデルでの同payload Evidenceを導く。

### NamedAccessible（8）
- `child_rank`【補助】: 任意のCoverageで選ばれた子edgeは固定journal rankを真に減少させる。
- `coverage_accessible`【補助】: 任意のCoverageとdomain内focusは選択子関係でAcc。有限domain・Acc・モデルを前提にしない。
- `covered_tree`【補助】: 任意のCoverageとfocusだけからNamedTree存在。
- `covered_dictionary`【健全性補助】: 上にSourceFormedを加え、一つのpayloadの全現在モデルEvidenceを導く。
- `actual_accessible`【補助・実例】: 既存scalar-input/named-output初期例の明示singleton coverageはAcc。
- `actual_uniform_dictionary`【健全性補助・実例】: 同coverageから一つのpayloadと全現在モデルEvidenceを構築。
- `actual_nonvacuous`【健全性補助・実例】: 同じpayloadのNamedTreeと明示現在モデル・Evidenceが共存。
- `actual_no_old_coverage`【補助・実例】: 同singletonについて旧Mixed局所Coverageは存在しない。

### BoundedAssembly（6）
- `enough_fuel`【補助】: 任意Coverage・focus・fuel>rankなら、assemblerのsome payloadと同payload NamedTreeが存在。
- `successful_tree`【健全性補助】: 任意fuelでassemble=some payloadなら、同payloadはNamedTree。
- `build_succeeds`【補助】: 任意Coverage/focusでrank+1を使うbuildは必ずsome payloadとNamedTreeを返す。
- `build_dictionary`【健全性補助】: 上にSourceFormedを加え、buildの同一payloadが全現在モデルでEvidenceを持つ。
- `zero_fuel`【補助】: 任意Coverage/focusでfuel0はnone。
- `actual_build`【補助・実例】: scalar-input/named-output実例のbuildは定義的にterminal payloadを返す。

### PathBound（6）
- `rank_budget`【補助】: 任意選択子経路で、edge数+終点rank≤始点rank。
- `length_le_rank`【補助】: 同経路のedge数≤始点rank。
- `length_le_ceiling`【補助】: 同経路のedge数≤固定journal最大親ID+1。
- `no_positive_cycle`【補助】: 同focusへ戻る選択子経路のedge数は0。
- `rank_zero_terminal`【補助】: rank0のcovered nodeのchildrenは空。
- `vertices_le_rank_succ`【補助】: rootを含めた経路vertex数≤始点rank+1。

### NamedCoveragePersistence（7）
- `node_transport`【補助】: packet membership保存とordinary Context Extensionから、同じkey/childrenの新局所Nodeが存在。
- `node_children`【補助】: その証明から選ぶ移送nodeは旧childrenと等しい。
- `node_key`【補助】: 同移送nodeは旧keyと等しい。
- `child_iff`【補助】: 移送Coverageの同じdomain上の子関係は旧関係と同値。
- `ordinary_children`【補助】: 実Shared OrdinaryStep列から同じ子関係の保存を導く。
- `ordinary_dictionary`【健全性補助】: 任意ordinary列・初期Coverage・covered focus・終点SourceFormedから、終点NamedTreeと全終点モデル共通payloadを導く。
- `ordinary_uniform_payload`【健全性補助】: 同じ前提で、一つのpayloadが始点と終点のNamedTreeを持ち、全終点モデルでEvidenceを持つ。初期モデル存在は仮定しない。

### AssemblyPersistence（8）
- `collect_congr`【補助】: 等しい順序つき需要一覧と、各要素で等しい依存callback結果からcollect結果の等式。
- `assemble_congr`【補助】: 同registry/domainの二Coverageが各nodeのkey/childrenで一致すれば、任意fuel/focusでOption Payload結果が一致。
- `extension_assemble`【補助】: packet保存とordinary extensionによるCoverage移送は、任意共通fuelのassemble結果を保存。
- `ordinary_assemble`【補助】: 実ordinary列について同じ計算結果保存。
- `collect_unique`【補助】: 同じ順序一覧で、各子の成功callback出力が一意なら、成功collect出力も一意。
- `successful_fuel_unique`【補助】: 同じCoverage/focusで二つのfuelがともに成功したらpayloadは等しい。fuelの大小関係を仮定しない。
- `extension_build`【補助】: ordinary extension下で、異なるrank上限を使うbuild同士も結果が一致。
- `ordinary_build`【補助】: 実ordinary列に沿った移送Coverageのbuildは元と等しい。

### AssemblySize（5）
- `node_degree`【補助】: 任意局所Nodeのchildren.length≤固定journal最大子数B。次数上限を仮定せず導く。
- `collect_bound`【補助】: 各成功callbackのpayload node数≤limitなら、成功collectの総node数≤一覧長×limit。
- `successful_bound`【補助】: 任意Coverage/focusでassemble fuel=some payloadなら、その全node数≤cap(B,fuel)。
- `build_bound`【補助】: 任意Coverage/focusのbuildは、node数≤cap(B,rank+1)を満たすpayloadを返す。NamedTree性は別のbuild_succeedsで検証済み。
- `actual_one_node`【補助・実例】: scalar-input/named-output実例のbuild出力node数は1。

### NamedSelection（5）
- `leaf_selected`【補助】: named LeafShape、可視checked宣言、metadata、実sourceモデル、同需要のLocal.selectedから、宣言keyと空childrenがselected key/listに一致。
- `tree_selected`【健全性補助】: SourceFormed NamedTree・実現在モデル・同需要のselectedから、key一致とselected順序の子Evidenceを導く。
- `terminal_payload`【補助】: 同現在モデルでEvidenceを持ちchildren=[]にselectedされた需要のpayloadは、そのkeyのterminal形に等しい。
- `leaf_tree_unique`【補助】: named LeafShapeと実現在モデル・selectedのもとで、同需要のすべてのNamedTree payloadはterminal形に等しい。
- `actual_unique`【補助・実例】: 既存named-output実例の現在モデル・NamedTreeが存在し、同需要の全NamedTree payloadはterminal形。

### NamedSpine（4）
- `branch_models`【健全性補助】: 有限nominal spine、実query/location、実named requestsの観察を持つShapeから、任意sourceモデルでBranchModelsを導く。
- `ready`【補助】: 同ShapeからRootDefinedと実generated schemaのunknown=falseを導く。モデル不要。
- `instance_of_shape`【健全性補助】: 同Shape・可視checked宣言・metadata・sourceモデルから空子一覧のInstanceを構築。
- `evidence_of_shape`【健全性補助】: 同じ前提からterminal Evidenceを構築。

### NamedSpineExample（8、すべて固定実例）
- `checked`【補助】: 新ternary nominal入力/named出力宣言のDeclarationChecked。
- `metadata`【補助】: 同registry/contextのMetadata。
- `actual_evidence`【健全性補助】: 同sourceの任意モデルでterminal Evidence。
- `nonvacuous`【健全性補助】: outputs非空、明示sourceモデル、同モデルEvidenceが共存。
- `registry_checked`【補助】: 同registryのChecked。
- `initial_source`【補助】: 同context/rootのInitialSource。
- `no_current_local_node`【補助】: 同初期tracked状態・rootについて今回の四constructor Nodeは存在しない。
- `coverage_gap`【補助】: InitialSource・実モデルとEvidence存在・同Node不存在を一つにまとめる。StableやV5反例は結論しない。

## 中間61定理sourceの独立検証

`9e1febb08784db6030756319bea1e3a682e65ddc` を新しいworktreeへ取得し、10moduleの既存oleanを取り除いた別libraryで全10moduleをtrust0再コンパイル、全14auditを実行してすべてexit0。275宣言gateも再度PASS。依存cacheは再利用している。61定理すべての公理出力と量化台帳の存在、manifestの10source blob SHAと公開SHAの一致を自動照合、missing0。統合Astraの小auditも30宣言を印字してexit0。

最新source-readbackと現在snapshot観察の相違をread-onlyで精査した。既存ObservedFiniteRequests.Treeはscalar/nominalだけで、record/variantは未対応。次の小さな接続は実report pathから正確なcurrent slot・target・descriptor順序を保持すること。詳細は[次回観察bridge](../design/2026-11-13-cycle170-next-observation-bridge.md)。新Astra成果をsnapshot証明書の完成とは数えない。


### NamedSpineStable（8、固定実例の補助・健全性補助）
- `initial_models`: 新registry/rootのinitial状態は同sourceモデルを持つ。
- `generated_root`: 新initial状態でGeneratedな需要はrootと等しい。
- `installs_committed`: 新rootから生成された任意のInstallable packetはすでにCommitted。slot0のnominal inputとNamedSpineの一般branch_modelsを使い、旧scalar-root安定性を使わない。
- `refresh_large_unknown`: 任意の意味保存refreshとID≥2について、新snapshotもそのIDをKnownにできない。同sourceの二つのモデルを使う。
- `feedback_stable`: 上のaction除外から新registry/rootの実Feedback Stableを示す。
- `stable`: 同じsourceのpoint-closureと実action包含からSupport Stableを示す。
- `shared_stable`: generic action包含を通じ、実Shared Stableを示す。異なるinstall終点を等しいとはしない。
- `stable_coverage_gap`: 同じ状態にSourceFormed・Shared Stable・明示現在モデル・Evidenceがありながら四constructor局所Nodeは存在しない。一般V5反例でも新非終端実行でもない。

後半の追加は、当初の「初期状態だけでStableとは限らない」という実質的な制限を解くために行った。旧10moduleの行を変更せず新moduleを追加した。一般NamedSpineの具体適用であり、固定例だけを独立したV5達成として数えない。


## 最終69定理sourceの独立検証とT7b

最終Lean sourceは `8d893bdc440a3e0255cd0bb8f742ac171ed3eb42`、tree `e6137cb47af49b30dbc07211fc867d032cfd7217`。新規11module・69公開定理。別worktreeの公開SHAから新規11moduleのoleanをすべて再生成してtrust0再コンパイルし、全16auditがexit0。CompleteGateは生成/privateを含む295宣言を検査してPASS。manifestの11blob SHA一致、69定理すべての公理出力存在を自動照合した。依存olean cacheは再利用しており全repository再buildではない。ログ: `notes/verification/cycle170-public-final-replay.log`。

最初の最終replay先はtmpfs容量不足でworktree作成に失敗した。空のファイル集合を成功としてしまう旧helperの欠陥を検出し、その結果は採用しなかった。workspace上へ移し、11module・16auditの存在件数assertを入れたhelperで再実行して上記成功を確認した。他サイクルのファイルは削除していない。

T7b read-only依存調査を実施。`dots-cycle-170-reachability.md`と`tools/ReachCycle170.lean`、3組のroots/TSV/summaryを保存した。抽象target rootsと既存conditional concrete rootから今回の295宣言への到達は各0、6個の今回entryから147/295（公開定理38）。これはV5接続の未達を明示するもので、未到達宣言の削除根拠ではない。V5は未証明、8/14未消去。調査用既存downstream moduleのfocused buildは682jobs PASS、各probeは120秒上限でexit0。
