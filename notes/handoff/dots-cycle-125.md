# Cycle125: actual RHS binders to computed source dictionary outputs

**一般sourceのB4Bridges V3: 未証明（未充填）12 / 全12。一般B4は未完成。**

予定起動は2026-11-11T20:27:19Z、実作業開始は20:49:58Z。終了・公開照合の
正確な時刻と実作業時間はcompleted heartbeatに記録する。期限は予定起動から
55分の21:22:19UTCに固定し、実作業開始から55分後へ延ばしていない。
予定起動から実作業まで約22.7分の遅れがあった。最初のsource公開は20:58頃で、
予定起動の25分地点より遅れたが、実作業開始から約8分で公開した。今回の二段階の
部分目標と最終検証・公開は、実作業の25分を超える。終了理由はI-15(a):
55分枠の中に検証・公開・報告・writer解放を含めるため。待機で時間を埋めていない。

## 復元と担当範囲

- fresh integration: `38c50cb4197d453983e9e8d4dbffd10fa413bf13`。
- 開始前のwork head: `4bd5272a9907b3d30960af882f219c5f80fec073`。
- cycle124のcompleted heartbeat、報告、次のRHS→ordinary termの課題を読み直した。
  writer解放済みで、前cycleと並行した書込みはない。crash復旧・source喪失はない。
- local source treeとintegrationの差はheartbeatだけだった。integrationを祖先へ
  取り込み、前cycleの完了状態を保持した。shared Lean cacheを再利用し、複製していない。
- inboxはACTIVE、hash `2631f8a557ab1a3b3551556a3f516746e3e8fa65`。
  21:04頃の再取得でも同じ。I-19は既に検証済み。I-18項目5を続け、Astra担当の
  宣言・状態の定義、spec、plan、lakefileは変更していない。

## 閉じた部分目標

1. **実RHSのoutput-only binderをordinary source termへ、20:51–20:58頃。**
   実associated provenanceのlookupから、明示RHSが正規化後の出力専用変数である
   場合だけ、`capture.outputs binder`という実source変数を計算する。独立Denotesと
   lookupのiff、関数性、checked宣言の実producer子との同一sourceを証明した。
   手渡しの任意の関連型意味関数は使わない。第一checkpointとして公開した。
2. **手渡しのoutput vectorを除去、20:57–21:11頃。** 実Stateのinjective source mapを
   有限探索し、global source IDをlocal slotへ戻す。探索のiff、termをsourceへ戻す
   soundness、各slotに対する実RHS denotationとのiffを証明した。`Inputs`には
   head・上下端・targetしかなく、output termも解釈証明も入っていない。`build`が
   全outputを計算し、一つでも未対応/未所在なら全packageをdeferする。
3. **実checked宣言と非空modelの回帰、20:53–21:11頃（上と重なる）。** `wrap`の
   RHSだけを実output binderへ変えた宣言をcheckedとして証明。異なるroot target3/4を
   残し、実際に式を記録した状態のmodelを一つ構成した。その全modelでroot出力と
   producer子の出力source2が同値となる。さらにglobal12→local2の非恒等source map、
   global2の不在、異なるtarget13/14、欠けたbinder sourceによる全体deferを検証した。
4. **最終検証と公開。** 四つの新module、39 public theoremを検証し、source全treeを
   read backして一致を確認した。単純な一例の分類器は追加していない。

## 主張の量化子と効く側

[全39定理の正確な型](dots-cycle-125-theorems.md)に暗黙parameterも併記した。
39は一般部品13件と具体回帰26件の監査件数であり、39本のB4を閉じたという意味ではない。

- **OutputBinderTerms、健全性・完全性の部品。** 任意roles、Declaration、Capture、
  associated-name一意性、name、TyTermについて、成功lookup iff 独立Denotes。
  Denotesは実Supplies explicit equation、正規化RHS、outputNames所属を要求する。
  任意Checked宣言と任意allocationで、同じsourceを持つ実producer clause/equationがある。
- **sourceSlot/compile、健全性・完全性の部品。** 任意State、source、local slotについて
  探索成功 iff state.source slot=source。任意宣言/captureとname一意性に対し、
  compileが`.var slot`を返す iff 実RHSが`.var (state.source slot)`をDenotesする。
  global IDとslot番号を混同する仮定はない。
- **buildとrecord、辞書出力の健全性。** 任意Inputsと成功build結果Located、任意最終
  Assignment/Models、任意output occurrenceについて、computed RHSの実provenanceと
  root targetとのCommon.Equivalentを得る。modelの存在は一般には主張せず、
  任意のhead適用性・feasibilityを証明したとも言わない。
- **Examples、補助・忠実性回帰。** 成功・defer、非恒等写像、繰返しtarget、実producer、
  非空modelの正例を含む。新しい主型性の一般定理はない。

## 未接続の境界

これは出力側の明示binderのpartial materializationであり、full TermInstancesではない。
headの普通の型への解釈、lower/upper/targetのlocation、Capture、allocationは入力のまま。
渡したDeclarationが実選択された同じkey/roleであることは、既存OutputPlan/Plan側で
結ぶ必要がある。このmodule単独では可視宣言の選択やrole一致を認定しない。

通常input変数はintervalなので端点を勝手に中心にしない。nominal/compound RHS、
positional default、input variableのbodyはdeferのまま。これは言語の拒否規則ではなく、
実装した部分の境界。producer childの存在は、そのchildが解決済みという証明ではない。
今回のchecked例のhead termも供給されたもので、nominal headのelaborationを証明していない。

## SourceBoundary全13項目

| Field | 現在の状態 | 残り |
| --- | --- | --- |
| Checked | 一般certificate定義あり | 完全checker、constructor/Common対応。 |
| Models | 一般shared-state定義あり | 完全な宣言/role modelではない。 |
| Step | MISSING | 一般状態更新・再生成。 |
| Stable | MISSING | EOFを含む兄弟fixpoint。 |
| Generated | 一般emission/Plan/lookup部品あり | 実candidate frame、freshness、一般materialization。 |
| RootPending | 一般partial snapshot定義あり | Neededの最小適用性を導いていない。 |
| RootK2 | 一般partial normalized定義あり | 実source正規化との対応。 |
| CandidateK2 | MISSING | 実candidate inspection。 |
| InspectionPending | 実source fieldはMISSING | V3 schemaは対応済み、実predicateなし。 |
| Survivor | MISSING | Planはhead照合・feasibility・選択ではない。 |
| Evidence | full role fieldはMISSING | 明示output binderの実term/slot生成は今回接続。head・一般RHS・実選択が未接続。 |
| Reorders | 一般定義あり | fixed入力の宣言/child/output順。最終state/candidate対応なし。 |
| DictionaryEquivalent | 一般source/payload構造定義あり | full boundaryの観察意味との接続。 |

## 検証と公開

- final focused build: **533 jobs、exit0**。四つの新moduleをすべて明示した。
- final scoped trust-zero audit: **39 public declarations、exit0**。
  許可されたpropext / Classical.choice / Quot.sound以外は0。Audit登録も全39件を確認。
- 全量化子のsignature出力: exit0。diff-only gate、git diff --check: exit0。
- [コマンドと出力全文](dots-cycle-125-verification.md)。途中のtimeout124や修正前の
  証明エラーは成功に含めていない。最終module import/buildの通常経路も通った。
- localのfull lake build、full Audit、監督役の独立AxiomGateは実行していない。

第一source checkpoint: [f3c0bc835b9ef6e90a053503aefafda5558f201c](https://github.com/momota1029/yulang/commit/f3c0bc835b9ef6e90a053503aefafda5558f201c)。
このexact commitのhosted proof/coreはsuccess。runner checkout SHAとfull build1375 jobsを確認した。

最終source: [4f7210f07e000b71c036427746a684306d9ca8fd](https://github.com/momota1029/yulang/commit/4f7210f07e000b71c036427746a684306d9ca8fd)。
source tree: `a6f09070c9dbdc3138f2b79bebf1d7cd0d23b4b8`。
**2411 tracked filesの全treeがlocalと一致**。最終sourceのhosted CI状況は下の追記に記録する。

sourceの差分はintegrationからheartbeat込み10path（四つの新module、三つのLean集約/文書、
設計ノートとINDEX、heartbeat）。報告三つを含め最終13path。GitHubアプリでblob hashを照合し、
非force・expected-headでwork/dots-mainだけへ公開した。公開済みtreeを取得して全体比較した。

## 制限、Yulang2照合、次の部分目標

project importのみのprobeも止まる時間帯があり、45/90/180秒などのbounded試行が
timeoutした。原因は確定していない。最後は通常focused buildと全39件のscoped auditが通った。
開始時heartbeatのupdatedには概算値がありwall-clockより先だったため、後続はdateの
実測へ修正した。途中心拍は20:59、21:08台に公開。完了心拍でwriterを解放する。

Yulang2は前cycleの境界報告を復元し、公開前にwork/dots-auditの
`y2-claims-role-boundaries-cycle-2.md`（hash9d17b670c28c04fcc74ba2476a7832d999bdbbf1）を
再取得してROLE-MORE-001〜008と実装経路を読んだ。旧advertised-whereを新specの候補前提へ
輸入していない。正本はspec06 §6.3の普通の型変数＋等式、output-onlyのユーザー決定。
新しいYulang2実機試験は実施していない。新質問ノートは0件で、残るnominal/interval/
defaultの意味を勝手に選んでいない。usage quotaは不明。開始時空き容量は未記録、終了前は
38GiB（df -hのAvailは38G）。古いcacheの削除や新しいcache複製はしていない。

次の最初の部分目標:
1. computed binder outputを、実OutputPlanの同じchecked visible declaration/key/roleと
   結び、Transactions.Validのoutput側を自動生成する。head側の残る入力は分離する。
2. head/default/compoundのordinary表現を用意し、任意TermInstancesの残りを縮める。
   interval中心やnominal符号化を選ぶ必要がある所では質問ノートで止める。
3. actual candidate inspectionからinvocation別Frameを導き、source生成/RefinesとStepを結ぶ。

## 最終sourceのhosted検証（21:15UTC確認）

exact source `4f7210f07e000b71c036427746a684306d9ca8fd`について:
- [core](https://github.com/momota1029/yulang/actions/runs/43101133821/job/130792600588): success。
- [proof](https://github.com/momota1029/yulang/actions/runs/43101133893/job/130792592923): success。
- runnerのcheckout SHA一致、**full build1378 jobs**、full Auditで今回の39宣言が
  すべて出力されたこと、許可外公理0を確認した。これはhosted検証であり、localの
  全体検証を実行したという意味ではない。監督役の独立AxiomGateは未実行。
- これ以後の変更は報告とheartbeatだけ。報告treeの再取得・全tree照合・最終時刻は
  completed heartbeatへ記録する。未公開sourceや続行中の検証を残さずwriterを解放する。
