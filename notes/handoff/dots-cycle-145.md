# dot cycle145 — 非空associated-output mergeと共通辞書モデル

**一般V5は6/14完了、8/14未証明のまま。** 24新規modules・230公開定理を検証。 今回は実mergeの共通モデル条件を正確に分解し、実Initialから到達する非空output mergeと辞書の正例を同じ状態で検証した。

## 復元・権限・時間

- scheduled/start 2026-11-12T16:27:19Z、終了上限17:22:19Z。ユーザー指定55分上限を長時間要求より優先。
- integration/m1-finalをfresh取得し `6cff680ccafc24ab298e1b890adcb6d7bba15034`。standing orders、inbox I25、AGENTSと関連rules、公開済みcycle144を再読。STOPなし、前144completed/writer解放を確認。
- work/dots-mainだけへ公開。Astra所有の一般State/Step/Stable/Generated、spec、plan、lake設定、凍結Audit.lean/README.mdは変更ゼロ。

## 主成果

### 1. 共通モデルを保持した実mergeの必要十分条件

任意roles/registry/state/siteを量化する`JointMerge`で、同じassignmentの完全recursive Evidenceは、旧Evidenceと追加outputAtomsの連言に正確に還元。BranchAtも、output targetが既存source域にある場合に同じiff。PreparedのLinkedからtarget域条件を回収できるので登録済みsite版では独立仮定を減らした。

実merge後Jointは、旧2alias classのpacket key一致と、**一つの**旧Models・両class全BranchAt・追加output等式を同時に満たすモデルの存在に同値。独立した2つのJointの存在証明を同一モデルだと扱っていない。`JointMergeResidual`は同じkeyの旧Joint2本からkey条件だけを除去し、残るShared条件と失敗条件を必要十分に示す。Support SourceFormed wrapperは、実guard/登録/novelty/Generated等を別途受け取ったときのみ実Stepを構成する。

`AliasJoint`では同じ共通モデルを登録済みaliasへrerootでき、reachable・stable・selectedなfocusのInstanceへ接続。一般Jointの存在自体は未証明。

### 2. 有限merge-only foldの意味論

既存merge transformerの有限foldについて、Models・完全Evidence・BranchAtを旧条件と累積output等式へ還元。実aliasesが逆順event辺＋旧辺になることを証明し、同じevent集合なら順序と重複が違ってもModels/Evidence/Jointが同値（Jointはsource域条件あり）。

これはmerge-only foldの結果。install/refresh/reobserveを挟む任意executorスケジュール、各eventのenabled性、停止、一般canonicalLocalOrderは証明していない。

### 3. scalar associated-outputを実materializationから導く

`ScalarMerge`は実generated.testsにある同名scalar requestからoutputAtomsを導き、抽象AssociatedMeaningを仮定せず完全Evidenceを運ぶ。

`ScalarJournalMerge`はcurrent Modelsのpacket意味論から**packet元context/registry**のscalar testsを読む。歴史packetをcurrent BranchAtにすり替えず、全current modelsでmerge等式を導出する。よってModelsの集合は変わらず、そのモデル集合上で完全Evidenceも変わらない。実到達例では同じ親packetが両子のrequestを持つため、この一般定理をそのまま適用した。

### 4. 到達可能性を混同しない非空output回帰

- manual positive: input1、IDs200/201、output targets1/3、checked terminal7の共通BranchAt・Joint・完全terminal辞書を構成。実support mergeの全guardとnoveltyも具体化したが、出発journalのSourceFormedは主張しない。
- sourceformed negative-scope: 親1がrole1子2個をemitする実Initial→parent install→guarded merge。2targetは異なり、両方向output等式は非空、final model・SourceFormed・V5 Reachableあり。registryには子実装がないので子のBranchAt/Joint/Instance/Evidenceは全モデルで不存在。これは診断用のscope例でV5反例ではない。
- sourceformed positive: 別registryにterminal7を追加し、同じ形式の実Initial→install→非空mergeを構成。その**同じfinish**でroot/子Jointと、任意のmerge後modelで完全root Evidence `node1[node7[],node7[]]` を証明。子2個のsource identity・順序・重複は保持。固定modelへ置き換えていない。実support Local selectedとClassifyも構成し、任意merge後modelでEvidenceを持つpayloadはこの順序付き木と同一であることまで閉じた。既に親が所有するallocationを使うcurrent Freshも証明した。子はまだ未commit、一般V5は主張しない。下記の通りこの分類済みmerge endpointはむしろ¬Stableと証明した。

`JointMergeJournalScope`はreserved target3だけをstrへ変えるモデルで、sourceは満たしてもscalar-int packetは満たさないことを示す。従ってそのpacketを含む空facts journalはSourceFormedでない。手でpacketを置いただけの例をactual reachable正例に数えない。

### 5. cycle144の失敗例は一般V5反例ではない

固定stable failed-child snapshotにはcompleted selected Classifyが無く、子EvidenceのAll₂前提も成立しない。DictionarySound/evidenceNodeの前提を満たさないことと、このsnapshotの全generated focusでnode含意が成立することを形式化した。Acc/Stableと完全辞書成功を同一視しない。

### 6. 分類成功は飽和ではないことを実Stepで確認

成功例の全journal Modelsは親packetのscalar requestsからoutputTarget10=int=source1を強制する。一方、raw contextでは両output targetをstrにしたモデルが成立し、RawEqual(outputTarget10,1)を反証する。

従って実administrative equateがenabledであり、完全Classify済みmerge endpointの**¬Stable**を証明した。さらにその一歩を実行したnext stateのSourceFormed・Reachable・モデル実在を構成し、全journalモデル集合と完全root Evidenceを保存。次stateでもroot/子の実support Local selectedと同じ完全Classifyを再構成した。次stateのStableは未証明。これは「分類成功＝飽和」を否定する具体例で、一般V5を否定するものではない。

## 一般境界・未証明範囲

| SourceBoundary項目 | 状態と制限 |
|---|---|
| Checked | 一般定義あり。個別宣言checkとID一意性。重なるhead間の意味的一貫性とは別 |
| Models | 一般定義あり。source/packet/site意味論とsupport ledger |
| Step | 一般定義あり。今回も実support install/merge使用 |
| Stable | 一般定義あり。分類済みpositive finishは¬Stable、次のequate後stateは未判定 |
| Generated | 一般定義あり。実emitted edgesとalias閉包 |
| RootPending | 一般定義あり。source lower-head保留 |
| RootK2 | 一般定義あり。source/feedback循環 |
| CandidateK2 | 一般定義あり。candidate inspection循環 |
| InspectionPending | 一般定義あり。既存pending＋SupportPending |
| Survivor | 一般定義あり。raw current候補とJointは別 |
| Evidence | 一般定義あり。source-indexed完全再帰辞書。一般橋は未完 |
| Reorders | 一般定義あり。今回のevent集合同値はこれの一般executor版ではない |
| DictionaryEquivalent | 一般定義あり。payload/source既存比較 |

閉じた6本: `closure, stepModels, frontierLocal, localIdentity, dictionaryRefl, initialReorders`。
未証明8本: `progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder, evidenceNode, generatedChildren`。

今回の成果はsoundness/補助分解/限定正負回帰。一般completeness・principalityを新たに証明したとは数えない。全public定理の完全な量化子・前提は[型索引](../design/2026-11-12-cycle145-theorem-inventory.md)、設計は[module guide](../design/2026-11-12-cycle145-alias-joint-module-guide.md)。

## 本来の残差と次サイクル

1. 一般reachable/stable/selectedのJointを導く。同じモデルとhistorical/currentの区別を保持する。
2. `SameInputs`のsemantic observation equivalenceから、実capture・recursive child interpretationのassociated-expression equivalenceへ橋を作る。`Checked`だけではcross-declaration coherenceは供給されない。今回scalar requestの場合だけは閉じた。
3. 両endpoint alias classが既にcommittedである実到達mergeを扱う。今回の親packetあり／子uncommitted回帰をそのケースと混同しない。
4. 実equate後のnext stateのStable/追加administrative progressや、既committed両classの到達mergeを進める。全merge後modelの辞書は今回閉じた。一般Progress/where accessibility/canonical orderはAstra所有のまま。

work/dots-auditの公開X1–X25 oracleを再取得して既存対応を確認。新Yulang2 runtime実行はしておらず、旧runtimeとのsource adequacy/provenance実装一致も未証明。

## 検証・公開記録


- 24新規Lean modules、230公開定理。定義/abbrevを含む280公開宣言のaudit集合と実source集合を一致確認。
- focused build: **760 jobs、exit 0**。全repo local buildとは区別。
- 24 sourceを各 `lake env lean --trust=0 -E warning` で直接検査: 全exit 0。
- `Audit/Cycle145.lean`: exit 0、280宣言、標準 `propext/Classical.choice/Quot.sound` のみ。
- 230公開定理の `#check @` 型索引: exit 0。全量化子と条件を公開。
- 公開source commitを別checkoutしno-build差分gate: exit 0。既存lean行の削除なし、禁止構文なし、凍結ファイル/設定/plan/spec変更なし。
- 一般性・共通model・history/current・実到達性・分類とStableの区別について独立レビューPASS。
- [検証ログ](../design/2026-11-12-cycle145-verification.md)にbuild/audit/direct全出力と修正履歴。

最終source: [ef314055](https://github.com/momota1029/yulang/commit/ef3140551d6b016a3af6a9e0c71c020005bccfcb)。公開tree `365a0da66bfd573098a08fbbce8f5bbd2e6cc061` は検証済みlocal treeと完全一致。各source checkpointでもtree/SHA比較し、切り詰めは検出されていない。integration ancestryも公開commitで確認した。

17:14:55 UTCにこの最終source commitのGitHub CI [proof](https://github.com/momota1029/yulang/actions/runs/43266961072/job/131352981693)・[core](https://github.com/momota1029/yulang/actions/runs/43266961053/job/131352966066) **両方success**を確認。以下の報告/心拍のみの後続commitはLean sourceを変えない。

### 心拍・中間公開（commit時刻 UTC）

| 時刻 | commit | 内容 |
|---|---|---|
| 16:32:17 | `1029fac3c` | 開始心拍 |
| 16:36:14 | `42bd52d47` | 6定理 |
| 16:42:16 | `e6589288d` | 26定理 |
| 16:49:22 | `4ba0a9d3f` | 64定理 |
| 16:57:43 | `fe393d447` | 158定理 |
| 17:04:24 | `a40b088c2` | 192定理 |
| 17:08:35 | `e18853e4e` | 215定理 |
| 17:12:24 | `ef3140551` | 最終source 230定理 |

初回心拍は開始直後に公開できず16:32:17となった。tree作成のauto-review timeout後、明示的に許された1回のretryで公開した。その後の公開間隔は10分以内。毎回blob承認をユーザーへ求める経路は使っていない。

### 再現コマンド

```sh
cd lean
lake build $(sed -n 's/^import //p' Audit/Cycle145.lean) --wfail
lake env lean --trust=0 Audit/Cycle145.lean
for m in $(sed -n 's/^import Yulang\\.//p' Audit/Cycle145.lean); do
  lake env lean --trust=0 -E warning "Yulang/$m.lean"
done
cd ..
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
```

### 公開commit no-build gate出力全文

```text
verify-lean: . @ ef3140551 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalCompletion.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalView.lean only appended (plus top import lines)
ok: lean/Audit/AstraConfluence.lean only appended (plus top import lines)
ok: lean/Audit/AstraOrder.lean only appended (plus top import lines)
ok: lean/Audit/Cycle136.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Finished.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Followup.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Formation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Joint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Refresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Terminal.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Tree.lean only appended (plus top import lines)
ok: lean/Audit/Cycle139.lean only appended (plus top import lines)
ok: lean/Audit/Cycle139Followup.lean only appended (plus top import lines)
ok: lean/Audit/Cycle140.lean only appended (plus top import lines)
ok: lean/Audit/Cycle141.lean only appended (plus top import lines)
ok: lean/Audit/Cycle141Recorded.lean only appended (plus top import lines)
ok: lean/Audit/Cycle142.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupport.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

```


最終報告・完了心拍作成: 2026-11-12T17:17:19.401359+00:00（開始から50.0分）。検証済みsource公開とfresh published-checkout差分検証は完了。全作業worker/build停止。後続は報告/心拍のみでLean source変更なし。
