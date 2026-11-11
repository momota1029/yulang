# Cycle127: source-only recipes to actual variable-declaration evidence

**一般sourceのB4Bridges V3: 未証明（未充填）12 / 全12。一般B4は未完成。**

開始2026-11-11T22:27:19Z。最新ユーザー指示に従い、検証・途中成果公開・報告・writer解放を
含む期限を23:22:19UTCに固定した。終了時刻と所要時間はcompleted heartbeatへ記録する。
文書の「55分まで実装を続ける」より、全作業を55分以内に終える指示を優先した。

## 今回閉じた部分目標

1. **同じ実宣言からheadとRHSを計算、22:29–22:34頃。** checked visible宣言の一意なkey/roleを
   使い、headとoutputを両方計算するlookupを接続した。独立MaterializesPlanとのiffを証明。
   任意の外部head predicateや、再帰的な手渡しHeads証明は入力から除いた。
2. **完全な有限木の準備と独立exactness、22:30–22:41頃。** 全canonical child occurrenceを
   一つ残らず照合するHeadless Recipeを実装。独立再帰Materializesとのiffと関数性を証明した。
   missing・extra・別identityのchildを捨てて成功にしない。固定入力でvisible/where順を変えても
   成功/失敗を含むPrepared全体・辞書・記録stateが同じとなる。
3. **capture実現を構成し、独立source意味へ、22:35–22:41頃。** 正規化したheadがbare変数なら
   元のheadにもその変数が現れる。この事実とchecked output-only制約から、input/outputの
   非交差と全inputのsingleton捕捉を導く。任意assignmentで具体的binderValuesを構成し、
   外部Realizes前提を除いた。実visible宣言・全子・head区間・実RHS出力等式だけを述べる
   独立Instanceへ、全batchの任意modelにおけるsource Evidenceを接続した。
4. **本物の成功例と限界、22:31–22:49頃。** binary変数headのchecked producerと、input変数
   RHSの終端leafを作った。source mapはslot+100、根のtarget103/104からproducer102を経て
   input100へ等式がつながる。共同modelを明示した。準備成功とRootPendingが両立する回帰、
   compatibleな不等identity区間で独立Instanceが成立してもcompilerはdeferする回帰を追加した。
5. **source Evidence自体の順序輸送、22:44–22:49頃。** 任意source Dictionaryの独立Instance
   Evidenceを、同じbinderValues・source frames・assignmentのままregistry Reordersの前後へ
   iffで移せる。準備で得た辞書だけに限定しない。
6. **source-slot vectorも計算、22:50以降。** State.sourceの単射性を使い、全endpoint/targetの
   位置を計算する。独立Availableとの正確な成功/失敗条件、有効Inputsの一意性、Linkedからの
   完全性を証明した。source-only Recipeの入力はoccurrence・選択key・child形状だけになり、
   位置/head/output/実現証明を手渡ししない全model source Evidenceへつなぐ。
7. **最新candidate部品との境界、22:45以降。** 新たに統合されたAstraのEmissionsReadyは
   root.outputs=[]を要求する。この現在の保守的な範囲では、今回の非空出力の成功fixtureは
   どのcandidate contextでもSurvivorにならないことを明示する。言語の拒否・保留・失敗の
   定理とはせず、candidate定義を変更しなかった。

上の時刻は実作業の概算で、検証と回帰作成が重なる。終了理由はI-15(a): 約50分のサイクル内で
追加証明・検証・複数の公開・報告まで行うため。25分時点では、新source-only入力の削減と
最新candidateとの接続境界の確認が残っていた。

## 状態の復元、最新指示と担当

- APIで前回heartbeat cycle126 completedとwriter releasedを確認した。前回報告を読み、
  workspaceと一つのLean cacheを継続した。crash復旧、未公開sourceの喪失、前writerとの並行書込はない。
- 毎回の取得とstanding orders/inbox読取を実施。開始integrationは51967e7524a05a9caa80cffbd8c8133e36ae8465。
  inboxはACTIVE、78b90e4349de7157ddf499e69638a51352451cb1。I-20の同入力需要の併合は
  項目4担当未定なので着手していない。I-19のV3は既存の検証済み結果を維持した。
- git transportのwork/dots-main追跡refは古いcycle119を示したため、現在のwriter判定には
  GitHub APIのheartbeat・refを使用した。APIの前headは72d144efa6a796e68c49dab8ae97c9007c4ea38f。
  古い追跡refだけを根拠にcrash扱いやbranch上書きをしていない。
- 22:45の再取得でintegrationがac106dc2d40da22a38d9908b5d1940d21cd2d7e0へ進み、Astraの
  candidate5moduleと設計追記を取得した。inboxは同hash/ACTIVE。ローカルへ取り込み、
  Audit/Yulangのappend競合を両方保持して解決した。Astraの既存定義は一行も変更していない。
- dotはI-18項目5のEvidence/Reordersのみ。Astra担当の1/2/3、未割当4、spec/plan/lake設定を変更しない。

## 主張の量化子と範囲

[公開定理全件の日本語文と正確な型](dots-cycle-127-theorems.md)に、暗黙引数込みの`#check @`と
各定理の効く側を記録する。今回の健全性・限定的完全性・補助の分類であり、一般B4の主型性や
未充填フィールドを閉じた意味ではない。

- 任意checked registry、state、各source occurrenceのframe、有限source recipe、準備成功treeに
  対し、一つのsource辞書witnessがあり、readbackが一致し、記録batchのすべてのmodelで
  独立InstanceのEvidenceを満たす。辞書はmodelによらず固定、binderValuesはassignmentごと。
- 独立Instanceは実visible宣言、同key/role、完全canonical子、共有binderValues、各headの
  引数区間、実explicit RHSと各targetの同値を述べる。lookup/Located/計算vector/任意の解釈関数は含まない。
- 独立再帰Materializesと部分compilerのiff、source-only Recipeの操作分解iff、独立Instanceへの
  一方向の健全性は別物である。compatibleな不等identity区間も独立Instanceを満たしうるため、
  後者をcompilerとの無条件iffとしない。
- visible/whereの順序不変は、同じsource state・frame・assignment・選択key・recipeの下。
  candidate探索順、異なる最終state、一般driverの順序独立ではない。
- source identitiesを持つDemand、capture/allocation/frame、そのprovenance/freshness、選択key、
  finite child形状は依然として入力。準備成功は候補選択やcaptureの発見ではない。
- prepareはhead既知guardを検査せず、role解決の代わりにはならない。候補解決側のguardは
  変更していない。fixtureでは準備成功とRootPendingが両立する。
  nominal/compound/default、中心を持たない一般区間は未対応でdeferする。
- 任意入力のmodel存在は結論しない。非空modelの証明は明示したchecked fixtureに対してだけ。

## SourceBoundary全13項目

| Field | 現在の状態 | 残り |
| --- | --- | --- |
| Checked | 一般certificate定義あり | 完全checker・constructor/Common対応。Astra項目1。 |
| Models | 一般shared-state定義あり | 完全な宣言/role modelではない。 |
| Step | MISSING | 一般状態更新と再生成、I-20の需要併合。担当未定。 |
| Stable | MISSING | EOFを含む兄弟fixpoint。 |
| Generated | 一般emission/Plan部品あり | source-only Recipeは全子を検査するが一般生成driverではない。frame/freshness未接続。 |
| RootPending | 一般partial snapshot定義あり | 全無名引数Needed。実lower-head正規化との一般対応。 |
| RootK2 | 一般partial normalized定義あり | complete coneとsource正規化、source解釈との対応。 |
| CandidateK2 | 一般carrier上の保守的partial判断あり | Astra新部品。root出力空、HeadReady・実boundsの再帰検査、constructor意味などの制限。完全fieldには未接続。 |
| InspectionPending | 一般carrier上のpartial判断あり | Astra新部品。candidate検査範囲とsource provenanceの対応が必要。 |
| Survivor | 一般carrier上のpartial判断あり | Astra新部品。root.outputs=[]の対応範囲では今回の非空出力treeと未接続。 |
| Evidence | supported-variableの独立source判断とall-model構成あり | 一般head/RHS、候補適用性、実frame生成、完全role modelとboundary代入は未達。 |
| Reorders | 一般構造定義あり | 固定入力で実行packageと独立source Evidenceの輸送を証明。最終state独立は未達。 |
| DictionaryEquivalent | 一般source/payload構造定義あり | full boundaryの観察意味との一般接続が必要。 |

## 検証・公開

検証結果の確定値、実行コマンドと出力全文は[検証記録](dots-cycle-127-verification.md)へ記録する。
local full lake build、local full Audit、監督役の独立AxiomGateは実行しない。focused buildと
今回の公開定理全件・runtime定義のtrust-zero監査を区別して記録する。

第一checkpoint: [883de7b1673172a7d1a0c413572e1b957bec14a6](https://github.com/momota1029/yulang/commit/883de7b1673172a7d1a0c413572e1b957bec14a6)。
22:44:58までに**2445 tracked files全件のpath/mode/type/blob SHA一致、truncated=false**を確認。
9新module、67公開定理、focused553jobs、全67件のscoped監査、diff gateがexit0。
exact commitのhosted core/proof成功、runner checkout一致、full1404jobs、full Audit8617出力、
今回67/67件の出力、許可外公理0も確認した。hosted結果でありlocal全体検証ではない。

最終sourceとreportのcommit/tree、全件readback、hosted CIの最終状態は末尾とcompleted heartbeatへ追記する。
公開はGitHubアプリのblob/tree/commitと非force expected-head更新でwork/dots-mainだけに行う。

## 制限、照合、次の最初の部分目標

Yulang2 work/dots-auditのROLE-MORE-001–008を再取得して読んだ。旧advertised-whereの挙動を
新specの候補前提へ輸入しない。正本はspec06§6.3と最新inbox。新しいYulang2実機試験はしていない。
新質問ノートは0。source位置検索以外のallocator・nominal意味・default・interval中心を独断で選ばなかった。

project importだけでも無出力timeout124となる時間帯があった。cycle125にも同型の記録があり、
原因は確定していない。並行処理を減らしてbounded focused checkをやり直した。timeoutや
修正前の証明/linterエラーをPASSには数えない。初回lake PATH不足も修正後の実コマンドと区別する。
GitHub CLIは未認証だったため読取に使わず、接続済みGitHubアプリで公開・照合した。

開始時空き38GiB。終了前の空きと所要時間は最終追記。cache複製・削除なし。usage quotaは不明。

次の候補:
1. **candidate側の実root-output coverageと接続。** 今回の出力package/source Evidenceを受ける
   EmissionsReady境界をAstra担当と合わせる。現行guardをdotが勝手に緩めない。これだけで
   frame provenance/freshness、constructor意味、pending guardの残りが閉じるとは言わない。
2. **source-only Recipeの形状/選択key/frameを実candidate結果から導く。** 今回取り除いた位置、
   head、output、Realizesに戻さず、残っている入力を一つずつ導く。
3. **未対応head/RHSの意味の接続。** nominal/compound/defaultや非singleton区間を扱うには
   source解釈との対応が必要。関連する設計判断は質問ノートの手順に従う。

## 最終sourceの確定結果（23:09UTC）

[ebea49a586d96b795f8194cb9f3c5811bc0c616c](https://github.com/momota1029/yulang/commit/ebea49a586d96b795f8194cb9f3c5811bc0c616c)
をwork/dots-mainへ非forceで公開。treeは70d662d46f87ccbac11c7f5381518f0ccdc63c35。
**2456 tracked files全件のpath/mode/type/blob SHA一致、truncated=false**を確認した。
15新module・100公開定理、focused566jobs exit0、全100件のscoped trust-zero audit exit0、
欠落0・許可外公理0。コメントのみ明確化後の2対象buildも555jobs exit0。
100件の正確な型を取得し、定理別報告に日本語の前提・量化子と併記した。

任意runtime evalと実行定義6件の専用auditは無出力timeout124だった。再実行せず未確認とし、
回帰定理の証明成功と混同しない。最初の100件auditもtimeout124だが、bounded再試行で
100/100件を得た。最終sourceのhosted core/proofは現時点実行中で、結果を別に追記する。

終了前空き37GiB、使用量上限不明。新しいsemantic policy・質問・担当外の実装は加えていない。

## 最終sourceのhosted結果（23:11UTC確認）

- [core success](https://github.com/momota1029/yulang/actions/runs/43117436529/job/130848934786)
- [proof success](https://github.com/momota1029/yulang/actions/runs/43117436547/job/130848934857)

両jobのcheckout logにexact source SHA ebea49a586d96b795f8194cb9f3c5811bc0c616cを確認。
full buildは1415jobs成功、full Auditの8935項目を抽出し、今回100/100定理が存在、
許可外公理0を確認した。source treeは2456 tracked files全件一致。
これはhostedでの検証結果であり、dotがlocal full build/Audit/AxiomGateを実行した意味ではない。

最終3報告のtree readbackとwriter解放時刻は、公開後のcompleted heartbeatに記録する。
source以後の差分はこの3報告とheartbeatのみとし、Lean sourceの追加変更はしない。

## 最終read-only照合で絞った次の接続契約（23:14UTC）

Candidateの`Prepared`とdictionaryの`Prepared`は別の型である。前者から後者を得るには、
root出力のcoverage以外にも、同じstate/frameで次を分けて示す必要がある。

- rootと全canonical childのLinkedはsource-slot検索を満たす方向に使えるが、
  それだけでvariable head/output compilerの成功までは出ない。
- candidateの`HeadReady`はinterval検査とSurvivesを述べる。今回の部分compilerに必要な
  captured endpointの**source ID一致**を、型のcompatible/equivalentから勝手に導かない。
  今回の不等identity回帰は、この二つの条件を同一視できないことを独立source意味で示す。
- selected keyと完全child列は同じ実宣言・同じcapture/allocationから来る必要がある。
  finite recipe自体の発見、frameのprovenance/freshness、全無名headのreadinessは依然別の義務。

従って次回も「EmissionsReadyのroot出力制限だけを外せば接続完了」と扱わない。
上記は残りの契約を読んだ分解であり、新しいSurvivor反例や一般driver定理を証明した主張ではない。

## 公開済み報告のreadback（23:16UTC）

3報告をca1013ded899e622bf84e19a49f028a85f15dc5aへ公開し、tree
ce51b8219ca041c336108c818a3afc91f06732f4の**2459 tracked files全件一致**を確認した。
再取得した定理報告本文もlocalと完全一致、100型blockを含む。source以後の差分は3報告と
heartbeatの4pathだけ。公開後diff-only gateとgit diff --checkもexit0。

このreadback記録を最後に追記し、最終report treeと解放時刻・全体所要時間は、直後の
completed heartbeatに記録する。検証と成果公開は約50分のサイクル内で完了し、55分上限を守る。
