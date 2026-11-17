# Cycle236 — exact where recursion and finite aggregate realization

開始2026-11-17 08:32:27 UTC。最終公開・照合時刻は完了応答で記録する。
初回integration d8f2f959。途中09:10に9222fe53を再読しmerge。
standing-orders/inbox I44継続、STOPなし。対象の稼働競合なし。
監督側mergeは235途中版だったため、衝突5ファイルは差分を確認し、
公開済み235最終版と236追記を保持して解消した。古い成果の削除はない。

## 復旧

前回235 completed/最終公開1a3b67aを照合。未公開の前回成果なし。
今回は環境再起動なし。前周期の証明を再構築したとは主張しない。

## 結果

### 実where再帰の境界を閉じた

- `MixedWhere236.accessible`: 任意registry、sourceから到達したstate、任意demandで、
  そのsnapshotの実Localが生成するChild関係にAccが成り立つ。
  Models非空・Stable・Available・GeneratedChildrenを仮定しない。
- `whereAccessible`: literal B4SkeletonV8の対応フィールドを満たす。
  selected親の登録済みidentityの有限上限と、各子identityが親より大きいことから証明。
- `MixedResolver236.tree/tree_exact/result_exact/proof_independent`: 任意checked registry、
  source到達snapshot、需要に対する正確な全順序付き木を構成し、分類と証明独立性を示す。
  これはClassicalな固定snapshot resolver。飽和executorでも辞書健全性の完成でもない。

### 行政的更新の停止性

- `MixedAdministrative236` は実refresh/equate/reobserve/mergeのguardをそのまま使う。
  元stateのraw sourceとcentered site出力から有限支持を作り、known/point/equality/aliasを追跡。
- `MixedAdministrativeOrder236.accessible`: 任意stateからこれら全更新のAcc。
  任意の有限poolを仮定しただけの主張ではなく、支持集合を構成している。
- `MixedProgressSplit236.split/quiet_accessible`: source到達traceには未記録enqueueがなく、
  全Stepは上の更新かplanを一つ増やすinstall。plan長不変の区間は停止する。
- `accessible_of_installation_descent`: 明示したInstallationDescent rankがある場合の全Step停止。
  rankの存在は未証明。全kernelの停止性を証明したとはしない。

### 実218終点の分類

`RootFrame236` は235の実fullStable終点の現在parentにFresh/Prepared/Unique/fullHoldsを接続。
`RootSelected236.selected` は具体的な一つのfinal modelからSafeKnownと衝突不存在を導き、
現在parentがnewChildだけを持つselectedであることを証明。
`Resolution236.old_rejected/new_pending/root_tree/root_result/no_root_success` は、
旧子がrejected、新子がpending、根がselected 0 [pending]、最終分類pendingを示す。
そのsnapshotの成功辞書分類はない。一般EvidenceNodeの反例とは主張しない。

### Choiceと実履歴

`MixedChoiceHistory236` は任意実source到達stateのstored packetについて可視性、site/role、
plan履歴との一致、各fullModelsが実stored packetを満たすことを証明。
`MixedChoice236` はchecked/roles一致/source到達/selectedの下で、ChoiceCompatibleを
全historical aliased declarationの現在Preparedと同値化し、現在Failedがないこととも同値化。
role-key一意registryの場合はChoiceを導出する。一般Choiceは未証明。
`Dependency236` は実aggregate sourceが自分の全RHS endpointより大きいこととWFを示す。
これを全履歴のfreshnessや全version数の有限性とは同一視しない。

### 構成的な同一modelと履歴再利用

- `FiniteEquationRealization236` / `SelectiveEquationRealization236`: 任意有限整合的entry群で、
  RHS支持poolを保全してpool外のtargetだけを書き換える明示的代入。
  pool内targetの既存等式が成り立てば、全entryの等式を同時に満たす。
- `AggregateRealization236` / `AggregateEntries236`: 実版付きmergeのentryとの正確な対応。
- `SemanticRawFrame236`、`HeadFrame236`、`ExpressionFrame236`、`PacketFrame236`、
  `JournalFrame236`: 任意二modelが明示的有限意味支持で一致すれば、実raw、schema、式、
  全packet、全journalの意味が同値。予約名だけの所有は意味支持と区別する。
  journal支持は全stored planとeffectのsnapshot/current両方を含む。
- `PrivateCompletion236` / `SemanticCompletion236` / `InitialCompletion236`:
  明示したfreshness、cross/self/projectionとraw modelからprivate headのモデルを構成。
  実初期sourceについてはbelow-seed条件からfreshnessと中心保存を導出する。
- `MixedFreshCompletion236` / `MixedSelectiveCompletion236` / `SelectiveAggregate236`:
  全journalとcurrent classを保全するfresh/再利用双方の具体的代入。
- `AggregateReuse236` / `AggregateLedger236`: 同seedの同aggregate IDは同じ式を表す。
  実stored planのfullModelsからmergeを取り出し、構文的ProtectedCoveredがあれば、
  pool内targetの既存等式を意味仮定ではなく実履歴から導く。
- `MixedLedgerCompletion236.simultaneous`: 任意state/current plan、一つのmodelについて、
  context一致、ProtectedCovered、journal Models、cross/self/projection/ClassEffectsの下で、
  同じ構成済みmodelがjournal Models・候補HeadModels・current ClassEffectsを同時に満たす。
  任意selected/sourceReachableからcoverageや共通modelを導出したとはしない。
  結論は候補全fullHoldsではない。
- `AggregateActual236` / `SelectiveActual236`: legacy/output/actual binder、actual変数・式を保存。
  selective版はFresh不要。出力schema・全childの成立自体は結論ではない。
- `MixedSelectedWitness236`: Models非空を明示したselectedからsharing feasibility、
  実ChosenHead witnessを明示したselectedからChosenEffects witness。
  別々に選んだ証人を無断で同一modelにはしていない。

## 受入条件と未完

I44の実後継境界でwhereAccessibleが閉じ、行政的停止性・共通modelの実構成が進んだ。
一般EvidenceNode、GeneratedChildren、全install停止性は未完成。
残る全体運用フィールドはprogress/execution/halted/treeExecution/canonicalLocalOrder。
新たな対象そのものの反例なし。言語意味の変更・質問ノート追加なし。
全32モジュールの宣言名は `notes/verification/cycle236/declarations.md`。
量化子・前提の正確な型は各Lean宣言に保存。391は監査したkernel constants数で定理数ではない。

## 次の優先3件

1. 実reachable/selectedからAggregateLedger236.ProtectedCoveredを導出する。
   legacy/journal/current/class支持に分解し、endpoint再利用の履歴を追跡する。
2. 同じmodelでactual HeadEquations、emitted output、全ordered childを満たしてfullHoldsへ接続。
   一般ChoiceCompatibleも残る。狭い断片を増やすだけでは完了にならない。
3. InstallationDescentの実rankを構成する。numeric slotの増加を有限version上限と誤認しない。
詳細は `notes/design/2026-11-17-cycle236-remaining-bridges.md`。

## Yulang2との照合

work/dots-auditのx-oracle X13–16とy2-claims-casts-rolesを再読した。
今回は初回作業前でなく途中の再読であり、その手順上の遅れを記録する。
旧実機の局所入力の成功・同頭の表示・区間近似は新versioned kernelの完全性を検証しない。
役割の再展開と安定後確定の文書方向は対応するが一般driverは未完成。
今回Yulang2実機を新規実行していない。新実装と全面一致したとは主張しない。

## 検証・運用

各新モジュール: `lake env lean --trust=0 -DwarningAsError=true Yulang/<module>.lean -o <focused olean>`。
4監査は106/114/125/46 constants、計391 constants・32 modules、許容公理は
propext/Classical.choice/Quot.soundだけ。全32 direct compileと4監査の最終再実行ログを添付。
全体lake build/verify-lean.shはstanding orderに従い未実行、監督役の全体gateに委ねる。
既存proof source、凍結Audit.lean/README.md、spec/plan/lakefileは変更なし。
barrelは32 import追記のみ。新Auditは別ファイル。独立レビューで論理的漏れ未検出。
途中成果cef57a6f、115be38bをGitHub appで公開し、それぞれ明示SHA取得後に全tree差分ゼロ。
最終公開も同じ確認を行う。CIの空statusをPASS扱いしない。使用量枠は不明。

最終成果固定: 2026-11-17 09:16:57 UTC、開始から44.5分。
最終4監査も全てexit0。全tree照合後の時刻と公開SHAは親への完了報告に記録。
ディスクは終了前2.2G使用/4.9G、空き2.8G。開始時測定は記録なし。

公開対象は前cycle235最終treeから計52ファイル（新Lean32、分割Audit4を含む）。
