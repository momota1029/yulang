# dots cycle161: 非terminalな親・子の現在Evidenceと、旧Evidenceの正確な境界

## 結果・未解決欄

V5は **8/14 open** のまま。
`progress / execution / halted / whereAccessible / treeExecution /
canonicalLocalOrder / evidenceNode / generatedChildren` は未証明。
一般B4、完全性、主型性、終了性を完成したとは報告しない。

今回、深さ2の非点capture collapseを、変数入力のwhere子を持つ非terminal親へ広げた。
materialization request全リストと生成schemaは不変だが、子の需要区間は変わる。
この区別をLeanで証明し、同じmodelでの親BranchModelsとInstanceを輸送した。
名前つきwhere出力がある場合も、正規化後の構文的scope条件から親を輸送できる。

実際のChecked registry・初期source・改善を伴うCertified reobserve Step・Reachable・
SourceFormed・現Modelsと、現child `node32[]` を含む親 `node31[node32[]]` の
Evidenceを一つの正の回帰で結んだ。現childの端点はbottom/intで同値ではない。
初期ordinary等式から全modelに対するexact性を導いており、結論を仮定して
Certifiedを作ったものではない。ただしselected、出力installation、Stableは未証明。

重要な負の結果も得た。同じ正例で旧・現の完全Evidenceを両立させようとしたが、
旧childの実際の引数はprivateなmerged IDなので旧source内に存在しない。
`root_no_evidence` は **全model・全payload** について旧root Evidenceがないと証明する。
したがって正例は「revision後のEvidenceの成立」であって、旧完全辞書の保存例ではない。
旧Evidenceを明示的に要求する条件付き輸送との矛盾もない。

## 復元・開始・担当範囲

開始2026-11-13T08:27:19Z、上限09:22:19Z。55分以内の検証・公開・報告を優先。
初回integrationは5a85451dd03f4de2a048c0219fea41e4a9cd7508。
standing-orders/inbox、I25、公開cycle160最終7309ee8c1a6dfbd56a404f2fd551ba65ee1dd703、
AGENTSと関連Yulang2監査を再読。前心拍completedとworker終了を確認して残存worktreeを再利用。
前cycleとの並行書き込みはない。AstraのState/Step/候補の定義は変更していない。

08:54頃の再fetchでintegrationが62cba43b580c5f0740fafd873a740a8a709643d9へ進み、
**I26: 片付いていないimpl出力を根拠にした展開は保留** を確認。
監督役のspec・inbox・B4草稿の3文書差分をそのままmergeした。ACTIVE継続。
この更新には新しいLeanガード定義は含まれていない。
既存source Evidenceは意味論の判断であり、実行時の選択許可と同一ではない。
既存Value.SupportPendingからLocal/B4 Local/Classifyのselectedを排除する3定理と、
子がsupport-pendingなら親の完全selected辞書を排除する1定理も追加した。
否定の排除にはroot-ready/no-K2前提は不要だが、正のpending分類はK2優先条件を保つ。
I26の新guard/Step/Stableを証明したとは報告しない。詳細はI26 boundary review note。

## 定理・前提・どの側か

全公開名の量化した型は `notes/verification/dots-cycle-161-signatures.txt`、
source SHA256とファイル対応は `dots-cycle-161-inventory.json`。
moduleごとの意味と限定は `notes/design/2026-11-13-cycle161-module-guide.md`。
以下は健全性に向けた条件付き輸送補助・独立補助・正負の回帰であり、完全性/主型性の主定理ではない。

- RequestSnapshot: 任意の固定allocationで、Revisionが保つseed/output captureの下に
  requestsの順序・重複を含む全リスト、generated schema、RequestReadyが不変。
- NonterminalNonpointBranch/Scope: 既存Shape、query一致、単一binder、変数に正規化する
  子入力、旧BranchModels・現source Modelsを同じmodelで持つと現BranchModels。
  名前つき子出力は正規化後scope（正規形/正規化後変数ならCheckedから導出）を保つ。
  leaf点性は不要。任意patternの正規化scope保存は今回証明していない。
- NonterminalNonpointEvidence/NamedEvidence: registry Checked・可視宣言・実際の旧Instanceと
  現Modelsから再計算した現Instance。親Evidenceには、本当に現時点で生成された子の
  Evidenceが別途必要。旧childを等しいと見なして流用しない。
- NonterminalRecordedRevision: reportを保つ制限付きの履歴と記録済みpacketから旧Instanceを
  既存不変条件で導出。最後のCertified collapseではreportが変わってよい。
  最後の実Stepを自動で供給する定理ではなく、一般Value履歴への拡張でもない。
- ChildCaptureTransport/Example: 子identity全リスト・出力targetは固定、入力Fitsは包含。
  実際に同じ子identityでも需要とFitsが真に変わる正例を構成。
- VariableIntervalLeaf: terminalなbare-variable子は、source Models・所在・端点の順序が
  あれば非点区間でもInstanceとなる。子rootの名前つき出力需要は空という限定がある。
- NamedExample: root関連出力とwhere名前つき出力の両方が実際に非空で、2つの
  generated variable useを持つ親BranchModels。子Evidenceや出力installationではない。
- CertifiedEvidence/OldObstruction: 上述した実Step後の完全な現Evidence、および旧Evidence
  不成立を別々に証明。sourceの所在とprivateな候補意味論を混同しない。

最後に、有限個の現childについて、可視Checked宣言・bare-variable query・実際の所在・
端点順序を記したLeafPlanから子Evidenceを導く一般補助を追加した。旧parent Instanceの
輸送とつないだ版、および制限付き記録履歴からparent Instanceを導く版も検証した。
後者は旧parent Evidenceも現child Evidenceも前提に取らず、Metadataもparent Instanceから
取り出す。ただしleafがterminalで名前つき出力需要が空、current所在/orderの計画が必要。
旧private IDが未所在という前述の反例を、この計画が無条件で満たすわけではない。
この一般補助は最後のrevisionの実Stepを要求/導出せず、SourceFormed/Stable/選択も
結論しない。実Step/Reachableを持つ具体的な正例とは区別する。

これらの深さ2・単一binder・変数入力・構文scope条件は証明断片の制限で、
新しい言語拒否規則ではない。

## SourceBoundary 13項目

|項目|現定義|残る区別|
|---|---|---|
|Checked|GeneralDeclarations.Checkedとroles一致|front-end adequacyとは別|
|Models|SaturationState.Models(current)|意味論の定義|
|Step|ValueSteps.Step|I26新guard実装・一般progress/execution未達|
|Stable|ValueSteps.Stable|guardやcurrent Evidenceを自動供給しない|
|Generated|SaturationState.Generated|一般選択子bridge未達|
|RootPending|NominalState.RootPending|現在context既知性|
|RootK2|FeedbackK2.RootK2|K2拒否が保留より優先|
|CandidateK2|FeedbackK2.CandidateK2|既存規則|
|InspectionPending|CycleK2/Value SupportPending|I26の新delayとの同値未証明|
|Survivor|RecursiveCandidates.Survivor|一般Evidence接続未達|
|Evidence|DictionaryRecursiveEvidence.Evidence|意味論であり実行許可とは別|
|Reorders|RegistryReordering.Reorders|canonicalLocalOrder未達|
|DictionaryEquivalent|DictionaryPayloadOrder.Equivalent|主定理全体ではない|

## 検証・失敗・制限

Lean4.35.0、focused buildと独立cacheのtrust-zero source replayを実施。
公開定理の全名・型・公理出力を照合し、private/generated宣言も依存公理gateで検査。
許可する公理はpropext/Classical.choice/Quot.soundのみ。
sorry、新axiom、native_decideなし。最終件数とログは終了時追記欄に置く。
全新moduleをYulang.leanからimport。root Audit/README/lake設定は凍結。
全体lake build、root Audit、全体verify-leanは実行していない。監督役の全体検証が必要。

差分限定 `verify-lean.sh --no-build` は最初、前cycle160最終で変更されたaudit gateを
復元したことにより凍結違反を検出。監督役の既存gateはそのまま戻し、前最終の完全gateを
新しい `Cycle160FinalDependencyGate.lean` に保存して再実行PASS。
既存証明を失わず、監督役統合版を優先した。collectAxiomsによる2つのreport-only
run_cmdはREVIEWとして記録される。証明や宣言を挿入する処理ではない。

試作でLean予約語prefixを変数名にして失敗し、pathへ修正して再検証PASS。
初期心拍のupdatedを未来時刻にした誤記は08:32:30に即修正。
未検証の試作や失敗を成功として数えていない。
第二checkpointのworkflow APIは空一覧。APIはPR-triggeredの先頭ページのみなので、
全CIの不存在や成功とは解釈しない。workspace空き39GiB、/tmp430MiB、使用量quota不明。

## Yulang2照合・次の境界

既存 `notes/audit/y2-claims-casts-roles.md` のY2-ROLE-003/004、spec6§6.3/6.5を照合。
型の再展開・lower/upper cross制約の方向を維持し、区間の中心を新設していない。
Yulang2 CLIはPATHに見つからず、今回は文書と既存監査のみ。新しい実機検証の主張はない。
I26は最新ユーザー決定を記載した監督役文書に従うが、旧Yulang2の規則と同一とはしない。

次は、実materialization後のsourceで旧childが所在する例と、記録済み親からの
一般current子Evidenceを分けて進める。旧private IDにsource所在を仮定して済ませない。
またAstraのI26ガードが届いたらInspectionPendingと実行選択の排除を接続する。
保留から意味論Evidenceそのものの否定を導く誤った橋は作らない。

## 公開checkpoint

- ecce490e9693afa81306ff330bfe2fb35e07e64a: request identity等。取得し直して固定localとの差は心拍のみ。
- 79f3a8f4a1bc2bdcb7c03680e45758f8d9967aff: named-output親・子の現Evidence・実Certified例。全tree差分は心拍のみ。

最終成果・監査・報告もwork/dots-mainのみへ公開し、不変commitを再取得して照合する。


## 最終source検証（09:06 UTC）

今回新規は18module・132公開定理。引き継いだcycle160のEmissionRequestIdentity
1module・3定理を含む最終検証対象は19module・135公開定理。
全19target focused build --wfail は775jobs PASS、独立cacheで全19sourceをtrust0再compile。
private/generatedも含む252宣言の依存公理gate PASS。監査ファイル19本PASS、
公開135名と監査出力の照合PASS、型一覧135個の出力EXIT0。
旧cycle160最終の577宣言gateも新名の監査ファイルとして保持・再実行PASS。
差分限定verify-lean --no-build PASS（report-only metaprogramming2件のREVIEWは明示）。

独立reviewで、旧/現のchild需要の区別、現childEvidenceの明示、registry keyの一意性、
leaf planの具体的な前提、最後のCertified revisionと実Stepの区別を確認した。
workerの証明作業は終了。残りは公開tree照合と最終報告のみ。
