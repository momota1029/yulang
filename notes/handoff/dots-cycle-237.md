# Cycle237 — semantic support and actual head/ancestry bridges

開始2026-11-17 09:31:36 UTC。前半・中盤checkpointと最終成果を以下に記録。
最新integration9222fe53、standing-orders/I44再読、STOPなし。
236最終a4f19c64とcompleted心拍、全tree一致を確認。復旧損失なし、稼働競合なし。
Yulang2 audit X13–16とrole003/004を開始時再読。旧実機の局所結果を新kernelの全体保証にしない。

## 最初の19モジュール

- 実refresh/reobserve/equateは全Modelsを保つため、以前の有限semantic supportをそのまま使える。
  install/mergeは新しいpacket/出力/全historical effectのcurrent classの支持だけを追加する。
  installのresidual frameは旧raw Modelsを既存journalから得るので、冗長なordinary atom支持や
  未使用raw slotをもう一度足さない。実source traceからそのsupport導出を構成した。
- reportのProjectionModels/cross/self checksは、実際のanchor/test/capture/checked endpointだけを読む。
  この正確な支持と任意の検証済みModelSupportに対するaggregate代入を接続。
  ProtectedCoveredから実stored equationが得られるが、一般coverage自体は未証明。
- actual head schema・HeadSharing・child actualschemaは既存selectivepatchで保たれる。
  任意current Frame/fullModels/privateHeadModels/actualheadSchemaから全capture Fitsを導出。
  全fullHoldsはHeadModels・actualheadSchema・Outputs・全child(Site.Holds＋actualschema)へ同値縮約。
  independent witnessesを同じmodelだとは仮定しない。出力・子の残件は明示したまま。
- 版付きactual headのweighted mass/readbackとchild semantic labelsを移植。
  InitialSource、point root、GroundRoots、Coverageの下で、実mixed traceの全modelと登録siteに
  depth＋ground label mass≤source mass。実installのcommon modelからenabled install depth boundを導出。
  旧fullHoldsや旧endpointagreementを前提にしていない。これは版数有限・全停止性とは別。
- 固定観測のordinary/context拡張による再構成planは履歴からCommittedを保つ。

## 検証と限界

19モジュールをdirect trust0/warningAsErrorで検証、174 constants監査PASS。定理数とは区別する。
全体lake build/verify-lean.shはstanding orderで未実行。
既存proof、凍結Audit.lean/README.md、spec/plan/lakefileは変更なし。
新たな対象反例は未確定。raw予約名の過剰支持とdescriptor付替えによる版増加は調査中の懸念で、
反例証明でも意味変更の根拠でもない。一般EvidenceNode/Choice/全install停止性は未完。
使用量枠不明。次のcheckpointで成果と限界を更新する。

## 第二 checkpoint

34モジュール、2監査174＋164＝338 constants PASS（定理数ではない）。
最初の19は1fd295eeに公開し、明示SHA fetch後に全tree一致確認。
追加成果:
- 有限semantic supportが全registered centered siteの名前も含むことを実traceで証明。
  小さいsupport版のselective代入もactual head/binderを保全し、全capture Fitsへ接続。
- 全stored packetのseed一致を実Stepで証明。target IDだけの履歴検索からProtectedCoveredへ進める。
  全historical aggregate entryは同IDなら同RHSでcoherent、RHSはtargetより小さい。
  WellFounded.fixで、任意外部assignment/全rowを保ちながら全historical merge等式だけを満たす
  一つのassignmentを構成。これは全journal Modelsの構成ではない。
- mode依存の実expression評価で正規化を保全し、shadowed fieldに余分なFitsを要求しない。
  checked.scopeにあるnormalized変数だけからchild lower≤actual≤upperを導出。
  実sourceReachable/currentFrame/fullModelsの下でfullHoldsを
  HeadModels・actualheadSchema・Outputs・全child actualschemaへ同値化。
  inputHolds/captureFits/childSiteFitsを別前提にはしていない。
- 実sourceのpoint/ground/Coverage条件から、全traceの登録center IDの固定有限coverを構成。
  最終状態のModels非空は不要。版非依存purposeの有限予約poolも導出。
  ただしaggregate版数有限はまだ証明していない。
- 初期設計の過剰raw支持を除いたModelSupport系列は独立査読で論理的漏れ未検出。

最新integration b8008c41を09:56再読、I44/停止条件に変更なし。
このintegrationは236の途中checkpointまでなので、236最終成果と237追加を失わず統合する。


## 最終追加成果（範囲を限定）

- SourceCenters237 は actual boundary.Initial の条件から ground/point/Coverage を抽出し、
  任意 sourceReachable 状態の全後続 trace に共通する center ID / generated demand ID の有限 cover を構成。
  aggregate の版、endpoint、occurrence、全状態の有限性を主張しない。
- ProspectiveEquations237 は同じ current context の一つの prospective plan を補助 ledger に加え、
  全歴史および現在 aggregate merge 等式を同時に満たす一つの assignment を構成。row は保存。
  ledger は operational successor ではなく、full Models / Installable の存在を主張しない。
- MixedMaterialization237 は actual sourceReachable 下で Installable を ChoiceCompatible と、
  一つの同じ model による old Models・private head・actual head・Outputs・全 child actual schema・Live
  の存在へ同値化。inputHolds/captureFits/childSiteFits は導出する。別々の存在証人を混同しない。
- HeadReplay237 は同じ seed/root/declaration で各入力が「現在 Point または旧 nonPoint」なら
  current Frame/full Models/private head から歴史 actual schema を再生する。旧 Point→新 nonPoint は未解決。
- CompoundEndpoint237 は variant(var) 子の lower が固定 purpose3 であること、および old/new Outputs が
  同じ model に成立すれば両 capture lower が同値であることを証明。差がある場合の current fullHolds 不能は
  条件付き局所障害であり、sourceReachable / Stable / EvidenceNode 反例ではない。
  次の actual fixture の必要 guard を別設計文書へ記録した。

## 残件と次サイクル

1. descriptor 付替えの局所 fixture を actual source からの最初の Installable/Step に接続し、
   反復 family が本当に構成できるか調べる。局所2stepだけで停止性を否定しない。
2. compound 固定 endpoint の障害を229のsource/233 reobserveから actual trace へ接続し、
   I44の履歴再生で回避できるか区別する。反例が確定した対象は停止・報告する。
3. id-only履歴lookup、ProtectedCovered、ChoiceCompatibleおよび全 journal/output/head の
   同一 common model を導出する。merge等式の共通解だけで一般EvidenceNode完了とはしない。

## 運用・検証

最新integration b8008c41を統合済。236途中までのintegrationとの差分5ファイルを確認し、
236最終成果・237追加を保持した。凍結 Audit.lean/README.md、旧proof、spec/plan/lakeは不変。
barrel は import 追記のみ。全体 lake build / verify-lean.sh は監督専用のため未実行。
新 Yulang2 実機検証なし、全体合意・CI通過を主張しない。使用量枠は不明。
最初19は1fd295ee、次34はd8623f963に公開、双方明示SHA fetch後の全tree一致を確認。
39モジュール時点で174+164+23=361 constants を許可axiom3種のみで監査済（定理数ではない）。
新規宣言一覧は notes/verification/cycle237/declarations.md。全量化と前提はLeanソースが正確な記録。


## 局所 retarget fixture の検証済み範囲

8モジュール Source/Packet/Frame/Full/RefreshBase/Refresh/Retarget/Next237。
Pair(Foo(Int),Foo(Int)) と終端 Pair(x,x) 宣言の installed fixture に具体 full Models を構成。
実 MixedKernel の refresh→reobserve 2step、各状態の full Models を検証した。
新 aggregate lower を nonPoint Foo(s,t) から Point Foo(s,s) へ改善しつつ、
既 Point の root descriptor を Pair(a,a) から Pair(lower,lower) へ付替える証明書が成立する。
次 current packet の bindings を厳密計算し、次 lower > 旧 lower、版の差、旧 upper との区別を証明。

重要: 原sourceから installed fixture への最初の guarded Step、SourceBoundary.Initial/GroundRoots、
第二 install、反復 family、無限 trace は未構成。InitialSource だけを sourceReachable と扱わない。
従って停止性・EvidenceNode の反証は未確定。意味変更をせず、次の必要guardを記録した。
第三監査23 constants/5modules、第四監査213 constants/8modulesで、
本サイクル計47モジュール・574 constants（生成定義込み、定理数ではない）。
各新モジュール direct trust0/warningAsError 検証、全constant公理監査は
propext/Classical.choice/Quot.sound のみ許容。sorry/new axiom/native_decideなし。

研究・検証区切り 2026-11-17 10:15:59 UTC、開始から44.4分。最終公開・全tree照合を続ける。終了時空き約2.7GiB、使用45%。

最終proof公開: `1e9aa8629ccb56d15642ddda4ff65551d87ce3a5`。GitHub connectorでlease付きref更新。
2026-11-17T10:16:28Z、明示SHA fetch後 `git diff --exit-code HEAD FETCH_HEAD` exit0、
remote work/dots-mainも同SHA。local proofcommit `4d1ce0e65`、tree `c9108196a8ba0235443dda2a0bd3f16f73d92bcb`。
combined statusは空配列、CI成功とは扱わない。completed心拍・この照合記録を追記。
完了処理時刻 2026-11-17T10:16:51Z、経過45.3分、55分上限内。全proof保持・作業tree cleanを確認。
