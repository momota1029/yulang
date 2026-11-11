# dots cycle 109 — 有限ordinary飽和の実行列を内側で生成

## 所要時間・部分目標

使用時間は約50分。開始 `2026-11-11T04:31:19Z`。正確な終了時刻・経過分はcompleted heartbeatに記録する。
**単独の部分目標は25分以内だが、復旧、4つの部分目標、独立な実行証明、最終検証を
つないだ全体は25分では収まらなかった。** 最初の目標を閉じて終了せず、次へ進んだ。

新規5モジュール、1,232行、公開定理77本。前回の未公開1モジュール269行・14定理も復旧した。
**閉じたのは既存の有限ordinary seed/split/trans規則のdriverであり、一般B4/T1cの完成ではない。**
一般B4の主要橋は5本とも未完。新しい意味論の判断0件、質問ノート0件。

- 復旧: 04:31〜04:37。cycle108の保存済み構造materializationを再検証して公開。
- 部分目標1: 04:37〜04:43。構造的な検出結果は1変数occurrenceにつき最大2回変わる、という一般の上限。
- 部分目標2: 04:43着手、04:45に焦点ビルド、04:54までに境界検証。構造的child領域と、完全な診断木の再利用・毎回のgraph再生成。
- 部分目標3: 部分目標2の検証中に着手、04:55に焦点ビルド、04:58に2と一括公開。実際の有限構造閉包からpaired evidenceを導く橋。
- 部分目標4: 04:58〜05:08。firstFreshが実際に選ぶ新しいcarrier indexから、ordinary状態列を内側で生成し、停止・モデル保存・再生成の上限へ接続。
- 最終の証明レビュー: 05:10〜05:13。各更新がその時点の既知premiseだけで可能だったことを、独立な帰納的Executionで証明。
- 最終検証・報告: その後。重なる検証時間があるため、上記の各区間は単純に足さない。

## 復旧と公開

開始時のheartbeatはcycle108、running、更新03:52:19Z、elapsed 28分で、cycle108の報告が無かった。
親から前writerの中断・停止を確認し、同時書き込みをしなかった。作業場は残り、
未公開local commit `7e89e9da7` はcleanだった。消去・reset・stashは行わず、その7ファイルを保存した。

- 復旧公開: `3a52eb5045d3756604325ba619d0ea306fa8d8dd`。
  CommonRoleStructuralOrdinaryMaterializationの316-job焦点ビルド、20 guard、4 kernel example、
  14定理の公理確認を再実行し、全てexit 0。失われたcommitted sourceはない。
  不明な未完成作業を復旧済みとは扱っていない。`notes/heartbeat/dots-main-crash-108.md`を公開した。
- 第1中間公開: `421c0df285b36589d5c4bd5b6e65dae8a524680e`。
- 第2中間公開: `9f25e92481280b8c434ffbe1ead394be6c8007d3`。
- ordinary trace公開: `4016e7d5c882f20f1c7b5abc079683639d50e08c`。
- **最終コード公開: `a9955de8fe4bcf325b241d2d02cdaeacd6f6bfd6`**。
  tree `2ef0fd9dc66c932773e71da2aafa5539cdc19cc9`。

全公開はGitHubアプリのblob/tree/commit APIとexpected-head付きnonforce ref更新で、
`work/dots-main`だけに行った。既存integrationへの書き込みはない。
各blob SHAをlocal git blobと照合。最終公開を明示的refspecで取得し、
`git diff --exit-code HEAD origin/work/dots-main -- lean notes/design` はexit 0。
最終コードtreeと上記SHAを取得して一致を確認した。
最終確認時のintegrationは `f243b114ca2ce0b6ff70f57eb07655b4b415d8db` で、local/public codeの祖先。
出発点5392aa937からの異なる公開pathは報告前15、報告を加えて16。
最後の公開では本報告とcompleted heartbeatだけを変える。

## 定理の正確な範囲とM1のどの側に効くか

### 1. CommonRoleStructuralMaterializationProgress — 補助、健全性側

任意n、実ordinary atom列A/B、Aの全atomがBに属するという前提、任意slotについて、
独立なpaired Evidenceが単調に増えることを証明した。検出のbudgetは、payload無し2、
異なるsyntaxが1つ1、複数syntax0。異なる単一payloadへの置換は起こらず、複数になれば戻らない。
`detector_equal_of_budget`、`goal_strict`は実際の検出・materialized Goalの変化だけを数える。

**`changes_bounded`**: 任意n、slots、元Goal、初期atom列、任意長の有限状態列で、
隣接するatom集合が包含関係にあるなら、元Goalのmaterializationの変化回数は
`2 * CommonRoleMaterializationProgress.potential original`以下。
potentialは元Goal内の変数occurrence数で、異なる変数名の数ではない。
モデル、整合性、impl一意性、payloadの深さ、成功辞書を仮定しない。
`computed_changes_bounded`は実際のState appendから状態列と包含を内側で作る。

2回という数は必要な保守性である。intのpaired boundsの後にint|intのpaired boundsを
足すと、同じCommonの意味でも異なるsyntaxが増え、検出がsome intからnoneへ戻る。
旧int-only版の「1回」と構文的fusionを構造版へ無断で持ち込んでいない。
これは言語の拒否規則ではなく、明示された保守的な検出器の性質である。

### 2. CommonRoleStructuralMaterializationDomain — 補助、有限領域の完全性側

任意の有限atom envelope E、任意の部分状態A（A⊆E）、slots、元Form/Goalについて、
AからmaterializeしたsyntaxがEから計算した有限paletteに入る。
任意registryと既存Checked証明について、そこからPaterson下降で生成する任意深さのchildも
有限domainに入る。`domain_exact`はpaletteのrootから独立Reachで届くこととのiff。
`run_work_present`は実graph入口の全診断ノードを覆い、outside・失敗branchも落とさない。

paletteはoccurrenceごとの組合せを含む過大近似で、同じsourceを別々に具体化できると
主張していない。domain membershipを辞書成功や候補選択として使わない。
未来の任意atom追加を固定したEで覆う定理でもない。有限batch jobではEを最終累積状態から内側で計算する。

### 3. CommonRoleStructuralFrontierReplay — 補助、実行保存の健全性/完全性側

任意の状態列（非単調・矛盾を含めてよい）で、`replay_snapshots`はキャッシュした完全な
診断木列が、各状態で実際にbuildし直した列と文字通り等しいと述べる。
再利用するのはmaterialized Goalが文字通り等しい場合の木だけ。
`runGraphs_exact`では全ordinary graphを各occurrenceで新しく作り、indexed old demandsを保つ。

**`runBatches_computed_bound`**: 任意registry/slots/Sources/元Goal、初期State、有限State batch列、
実runBatchesが返したoutputについて、実appendで計算したtraceと最終状態から有限domainを作り、
全snapshotと全childがdomain内、rebuild数≤1+2*元変数occurrence数、
visits≤その数*domain長を証明。domain長は重複・child位置を数える。
callerのChain、model、状態列、仕事領域、checker proofを実行に渡さない。

`runBatches_exists_iff`の成功は**ordinary整合性と宣言check**であり、全role解決ではない。
未完成の診断木があってもreportは返る。ordinary inconsistencyとrole failureを混同しない。

### 4. CommonRoleDerivedStructuralMaterialization — 健全性/有限規則内の完全性側

任意atom列、slot、closed Formについて、`detect_exact`は検出some f iff
独立seed/split/trans Derivesで上下のpaired boundsが導け、decodeがfになり、
他のそのようなpayloadが全てfと等しいことを述べる。
ordinaryの一般の意味的entailment全体に対する完全性ではない。

任意の元Stateモデルで`materialize_meaning`は全Formの意味を保ち、
`runState_models_exact`は任意の元assignmentに対し、実graph familyの表現可能性と、
元ordinary atomを満たすこと・old shared demands・独立な再生成frontier Derivesとのiffを与える。
`runState_graph_reflects`は任意のgraph実現モデルから元atomと元Form意味を反映する。
選ばれた1個のsolver witnessだけの主張ではない。

このrunはclosureを内側で計算するが、有限batch列自体はまだ外部入力だった。
次のモジュールが既存ordinary規則の範囲でその列も内側に移す。

### 5. CommonRoleStructuralSaturationTrace — 有限ordinary driverの補助/健全性/完全性側

**callerはregistry、slots、invocation Sources、元Goal、初期のchecked Stateだけを渡す。**
finite carrier、fuel、batch列、伝播済みatom、状態列、model、成功辞書は渡さない。

- `discoveries_result`: 任意有限Horn rule列/universe、任意内部capacity/seenで、
  実firstFreshのdiscovery列を逆順にseenへつないだものが、既存FiniteHorn.runの結果と文字通り等しい。
  public入口のcapacityは初期atomから計算する。外部fuelの定理を最上位完成の代わりにしていない。
- **`final_membership`**: 任意n、初期atom列、任意atomで、最終生成状態へのmembership iff
  独立seed/split/trans Derives。構文から生成した有限carrierの境界をcallerの仮定にしていない。
- `terminal_closed`: 実際の終了cacheにはenabledで未訪問のcarrier indexが残らない。
  role treeが一時的に変わらないことを停止条件にはしていない。
- **`generated_execution_complete`**: 初期atomから生成する実discovery列は、
  独立な帰納的Executionの各stepで「直前cacheには無い」「premiseが直前cacheに揃う」を満たし、
  最後にterminal_closedを満たす。最終閉包で導けるというだけで途中の因果関係を済ませない。
- `snapshot_models`: 任意初期atom列、実生成列中の任意snapshot、任意Common assignmentで、
  snapshotを満たすiff元atomを満たす。矛盾入力についても成り立つ。
  実driverは元Stateを実ordinary solverで検査し、この同値が以後の全状態に使える。
- **`run_computed_bound`**: 任意registry/slots/Sources/元Goal/初期Stateと、実runの返却outputに対し、
  計算された仕事領域、snapshot数≤1+初期atomとその構文carrierの長さ、
  rebuild数≤1+2*元変数occurrence数、visits上限、全snapshotの全child包含を証明。
- `runGraphs_exact`と`snapshot_graph_models_exact`: 全生成occurrenceの新しいgraphが
  実公開入口の結果と等しく、そのモデルのiffは元ordinary assignmentについて成り立つ。
- `final_materialize`: discovery順と旧cache順が違っても、最後のmaterialized Formは
  既存normalizeを元状態に適用した観測と文字通り等しい。

freshなのは**carrier index**である。同じatomが異なるindexに現れうるので、
atomが常に新しいと誤って主張せず、順序・重複を保持する。

## 仕様上の制限と未達

- Checked/Patersonは既存の有限宣言checkerの条件。新しい言語上の拒否を追加していない。
- uniqueな**構文**payload、closed int/pair/join/tick、既存seed/split/trans規則への制限は
  実装断片の制限であり、言語の完全性や最終拒否規則ではない。各docstringにも明記した。
- raw graph adapterはjoin/tickを扱うが、checked Stateのupper term grammarは既存のまま。
  対称なjoin/tick boundsを勝手にchecked ordinary solverへ入れていない。
- source slot map、invocation Sources、scope解決済みのGoal/Stateはまだ入力。
  parser、一般式/宣言lowering、動的fresh allocatorは未接続。
- 今回のdriverはordinaryの有限導出だけ。role候補から生成される新しい関連等式をordinaryへ返す
  **一般の相互フィードバック**、新しいsource名、K2、ファイル末尾の4分類は未完。
- frontierの独立Derivesはmaterialized Goalについて述べる。構文的候補集合が元Goalと同じとは言わない。
- dictionaryの言語レベルの観察同値・全モデル健全性、M1全体の主型性は証明していない。
  X13〜X16の一般外側入口をPROVEDへ更新していない。

残る主要橋は `source_boundary_adequate`、`generated_work_closed`、
`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound` の5本。
今回、2・3の既存有限ordinary断片を実行列まで接続したが、一般形を閉じたとは数えない。

## Yulang2との照合

着手前にwork/dots-auditの`notes/audit/y2-claims-role-boundaries-cycle-2.md`を読み、
ROLE-MORE-001/002（候補の順序を変えても曖昧、具体head優先をしない）と
003/005（旧whereの挙動と新spec6.3の差）を確認した。
旧実機記録の対象はd4c8bc8fc8a49173180932cd25921a2c41057354。
新しいYulang2実行は行っていない。構造unionの同値は既存Commonの証明を用い、
Yulang2の古いwhere挙動を新しい意味論として採用していない。

## 検証と制限

最終コードで、焦点368 jobs、61 executable guard、13 kernel example、
77公開定理の公理表示、5新モジュールの**全329宣言**のscoped allowlistがPASS。
全宣言gateは補助定義・private定理も含む。許容公理は既存3種だけ。
全体lake build、全Audit、build付きverify-leanは常設指示により実行していない。
以下のverify-lean PASSはdiff-onlyであり、全体PASSではない。

- cold dependencyの焦点ビルドが180秒でexit124。進んだ依存ビルドをcacheして再開し、
  依存を通した後、局所の型合わせを修正して367 jobsが完了した。
- 深さ16のgraphを含む境界suiteの初回はharnessの型/識別子誤りでexit1。修正後の
  stress版は180秒でexit124となった。深さ4の完全graph/driver suiteをPASSにし、decoder自体は深さ64も検証。
  深さ16 graphのruntime性能・完了を確認済みとはしない。定理は深さを固定していない。
- 初期中間公開のAuditにimport位置の誤りがあった。9f25e9248までに修正し、最終Auditのimportが
  冒頭だけであること、77定理の全登録を静的確認した。最終scoped gateとdiff gateもPASS。
- GitHub combined-statusを最終コードSHAに照会した結果はstatuses=[]。外部CIのPASSは確認していない。
- 空き容量: 開始47GiB、最終確認45GiB。前回・別作業の未公開物を削除していない。使用量枠は不明。

### 最終実行コマンドと出力

環境のPATHは `/workspace/scratch/1d0b4aaa3394/lean-toolchain/lean-4.35.0-linux/bin` を先頭に設定。
全Leanコマンドは`lean/`で、各回90〜180秒のtimeout付き。長い実行はsession/logで追跡した。

```text
lake build Yulang.CommonRoleStructuralSaturationTrace --wfail
lake env lean --trust=0 ../../cache/yulang109/scoped-axiom-gate.lean
lake env lean --trust=0 ../../cache/yulang109/final-boundary.lean
✔ [368/368] Built Yulang.CommonRoleStructuralSaturationTrace (1.3s)
Build completed successfully (368 jobs).
Scoped allowlist passed for 329 declarations from five new modules
exit 0
```

```text
lake env lean --trust=0 ../../cache/yulang109/final-axioms.lean
'Yulang.CommonRoleStructuralMaterializationProgress.evidence_mono' depends on axioms: [propext]
'Yulang.CommonRoleStructuralMaterializationProgress.detected_nonempty' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.nonempty_mono' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.detected_same' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.conflict_persists' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.budget_le_two' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.budget_mono' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.detector_equal_of_budget' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.form_budget_mono' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.form_budget_bound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.form_equal_of_budget' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.arguments_budget_mono' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.arguments_budget_bound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.arguments_equal_of_budget' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.goal_equal_of_budget' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.goal_strict' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.changes_with_remaining' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.changes_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationProgress.computed_chain' depends on axioms: [propext]
'Yulang.CommonRoleStructuralMaterializationProgress.computed_changes_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.materialize_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.arguments_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.goal_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.domain_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.regenerated_reach_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.domain_child_closed' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.workDomain_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.run_work_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMaterializationDomain.trace_includes_final' depends on axioms: [propext]
'Yulang.CommonRoleStructuralFrontierReplay.replayFrom_snapshots' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.replay_snapshots' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.replayFrom_rebuilds' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.replay_rebuilds' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.run_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.run_graph_snapshots' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.refreshGraphs_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.runGraphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.nodeCount_le_domain' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.replayFrom_visits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.replay_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.replay_work_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.runBatches_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.runBatches_exists_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.batches_covered' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.runBatches_computed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralFrontierReplay.runBatchGraphs_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.evidence_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.detect_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.normalize_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.materialize_meaning' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.materialize_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.materialize_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.normalized_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.computed_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.computed_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.run_computed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.runState_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDerivedStructuralMaterialization.runState_graph_reflects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.discoveries_result' depends on axioms: [propext]
'Yulang.CommonRoleStructuralSaturationTrace.discoveries_length' depends on axioms: [propext]
'Yulang.CommonRoleStructuralSaturationTrace.final_membership' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.generated_length' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.terminal_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.final_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.accumulate_length' depends on axioms: [propext]
'Yulang.CommonRoleStructuralSaturationTrace.accumulate_chain' does not depend on any axioms
'Yulang.CommonRoleStructuralSaturationTrace.accumulate_cover' depends on axioms: [propext]
'Yulang.CommonRoleStructuralSaturationTrace.accumulate_original' depends on axioms: [propext]
'Yulang.CommonRoleStructuralSaturationTrace.snapshot_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.run_computed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.final_materialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.snapshot_graph_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.runGraphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.discoveries_execution' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralSaturationTrace.generated_execution_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: yulang @ 52b3bd9e7 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

## 次の最初の部分目標候補

1. この有限ordinary driverへ、実宣言から生成する関連型/whereの新しいordinary atomを返す
   mutual feedbackを接続する。初期syntax carrierを越える型構造・source名をどう有限に覆うかが残る。
2. slotsとinvocation Sourcesを実source occurrenceから導き、generated childのsource identityを閉じる。
   既存boundary ledgerの未決を任意mapの仮定で隠さない。
3. 完成した安定frontierの保持されたchild診断を、承認済みの独立4分類とK2へ接続する。

停止理由は(a) 約50分のサイクル枠。設計未決を独断で埋めたり、早いplateauで停止したりしていない。
最終コード以後は検証・報告だけで、次サイクルを先取りして作業を広げない。

## 公開定理一覧

以下は上の量化・前提・断片境界の下で読む。単独の補助定理を一般B4完成と読み替えない。

### CommonRoleStructuralMaterializationProgress

`evidence_mono`, `detected_nonempty`, `nonempty_mono`, `detected_same`, `conflict_persists`, `budget_le_two`, `budget_mono`, `detector_equal_of_budget`, `form_budget_mono`, `form_budget_bound`, `form_equal_of_budget`, `arguments_budget_mono`, `arguments_budget_bound`, `arguments_equal_of_budget`, `goal_equal_of_budget`, `goal_strict`, `changes_with_remaining`, `changes_bounded`, `computed_chain`, `computed_changes_bounded`.

### CommonRoleStructuralMaterializationDomain

`materialize_present`, `arguments_present`, `goal_present`, `domain_exact`, `regenerated_reach_present`, `domain_child_closed`, `workDomain_exact`, `run_work_present`, `trace_includes_final`.

### CommonRoleStructuralFrontierReplay

`replayFrom_snapshots`, `replay_snapshots`, `replayFrom_rebuilds`, `replay_rebuilds`, `run_exact`, `run_graph_snapshots`, `refreshGraphs_exact`, `runGraphs_exact`, `nodeCount_le_domain`, `replayFrom_visits`, `replay_bounded`, `replay_work_present`, `runBatches_exact`, `runBatches_exists_iff`, `batches_covered`, `runBatches_computed_bound`, `runBatchGraphs_exact`.

### CommonRoleDerivedStructuralMaterialization

`evidence_exact`, `detect_exact`, `normalize_mono`, `materialize_meaning`, `materialize_normalize`, `materialize_congr`, `normalized_chain`, `computed_chain`, `computed_covered`, `run_exact`, `run_computed_bound`, `runState_models_exact`, `runState_graph_reflects`.

### CommonRoleStructuralSaturationTrace

`discoveries_result`, `discoveries_length`, `final_membership`, `generated_length`, `terminal_closed`, `final_models`, `accumulate_length`, `accumulate_chain`, `accumulate_cover`, `accumulate_original`, `snapshot_models`, `run_exact`, `run_computed_bound`, `final_materialize`, `snapshot_graph_models_exact`, `runGraphs_exact`, `discoveries_execution`, `generated_execution_complete`.

## 再実行用の最終境界suite（61 guard・13 kernel example）

```lean
import Yulang.CommonRoleStructuralSaturationTrace
namespace Cycle109Progress
open Yulang CommonRoleCaptureNormalization
open CommonRoleStructuralOrdinaryMaterialization
open CommonRoleStructuralMaterializationProgress
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
def slot : Fin 1 := 0
def slots (_ : Nat) : Fin 1 := 0
def lower (f : Form) : TyTerm (Fin 1) := CommonRoleIntervalDictionaryCompilation.lower slots f
def eqs (f : Form) : List (Atom (Fin 1)) := [.tyLe (.var slot) (lower f),.tyLe (lower f) (.var slot)]
def a := eqs .int
def b := a ++ eqs (.join .int .int)
def c := b ++ eqs (.pair .int .int)
def goal : CommonRoleIntervalPaterson.Goal := ⟨0,[(.var 0,.var 0)]⟩
def deep : Nat → Form | 0 => .int | k+1 => .pair .int (.tick (deep k))
#guard budget [] slot = 2
#guard budget a slot = 1
#guard budget b slot = 0
#guard budget c slot = 0
#guard detect a slot = some .int
#guard detect b slot = none
#guard detect c slot = none
#guard detect (eqs (deep 64)) slot = some (deep 64)
#guard budget (eqs (deep 64)) slot = 1
#guard materialize a slots (.var 0) = .int
#guard materialize b slots (.var 0) = .var 0
#guard changes slots goal [] [[],a,a,b,b,c] = 2
#guard changes slots goal [] [[],[],[]] = 0
#guard changes slots goal a [a.reverse,a ++ a] = 0
#guard changes slots goal a [a,[],a,[],a] = 4
#guard CommonRoleMaterializationProgress.potential goal = 2
#guard potential [] slots goal = 4
#guard potential a slots goal = 2
#guard potential b slots goal = 0
#guard budget (eqs (deep 64) ++ eqs (deep 64)) slot = 1
example : materialize b slots (materialize a slots (.var 0)) ≠ materialize b slots (.var 0) := by decide +kernel
example : Included a b := by intro x h; exact List.mem_append_left _ h
example : Chain [] [a,b,c] := by
  refine ⟨?_,?_,?_,trivial⟩
  · intro x h; cases h
  · intro x h; exact List.mem_append_left _ h
  · intro x h; exact List.mem_append_left _ h
example (before after : List (Atom (Fin 1))) (inc : Included before after) :
    budget after slot ≤ budget before slot := budget_mono inc slot
example (initial : List (Atom (Fin 1))) (states : List (List (Atom (Fin 1)))) (inc : Chain initial states) :
    changes slots goal initial states ≤ 4 := changes_bounded slots goal initial states inc
example (initial : CommonRoleSettledConstraints.State 1)
    (batches : List (CommonRoleSettledConstraints.State 1)) :
    changes slots goal initial.atoms ((CommonRoleCheckedOrdinaryReplay.trace initial batches).map
      CommonRoleSettledConstraints.State.atoms) ≤ 4 := computed_changes_bounded slots goal initial batches
end Cycle109Progress
namespace Cycle109Replay
open Yulang CommonRoleCaptureNormalization
open Cycle109Progress (slot slots eqs)
open CommonRoleStructuralOrdinaryMaterialization (materializeGoal)
open CommonRoleStructuralFrontierReplay
open CommonRoleStructuralMaterializationDomain (workDomain)
open PresenceNormalForm (Atom)
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def shrink : CommonRoleStablePaterson.Declaration := ⟨0,0,[.pair .int (.var 0)],[(0,[.var 0])]⟩
def leaf : CommonRoleStablePaterson.Declaration := ⟨0,1,[.int],[]⟩
def registry := [shrink,leaf]
def sources : CommonRoleGuardedIntervalPlans.Sources := fun _ d x => d.key * 10 + x
def goal : CommonRoleIntervalPaterson.Goal := ⟨0,[(.var 0,.var 0)]⟩
def nest : Nat → Form | 0 => .int | k+1 => .pair .int (nest k)
def payload := eqs (nest 4)
def conflict := payload ++ eqs .int
def states := [[],payload,payload,conflict,conflict]
def result := run registry slots sources goal [] states
#guard registry.all CommonRoleStablePaterson.check = true
#guard result.map Replay.rebuilds = some 3
#guard result.map (fun r => r.snapshots.length) = some 6
#guard result.map (fun r => r.snapshots.map nodeCount) = some [1,1,5,5,1,1]
#guard result.map Replay.visits = some 7
#guard (run registry slots sources goal payload [payload.reverse,payload ++ payload]).map Replay.rebuilds = some 1
#guard (run registry slots sources goal [] [[]]).map Replay.rebuilds = some 1
#guard (workDomain registry conflict slots goal).isSome
#guard (workDomain registry conflict slots goal).map (fun bound =>
  decide ((CommonRoleIntervalPaterson.Goal.mk 0 [(.int,.int)]) ∈ bound)) = some true
#guard (workDomain registry conflict slots goal).map (fun bound => decide (materializeGoal payload slots goal ∈ bound)) = some true
#guard (runGraphs registry slots sources goal [] states (fun _ => [])).map
  (fun output => output.2.length) = some 6
#guard (refreshGraphs (n := 1) (fun _ => []) [[]] []).isNone
#guard (refreshGraphs (n := 1) (fun _ => []) [] []).isSome

def badDecl : CommonRoleStablePaterson.Declaration := ⟨0,2,[.var 0],[(0,[.var 0])]⟩
#guard CommonRoleStablePaterson.check badDecl = false
#guard (run [badDecl] slots sources goal [] states).isNone
#guard (workDomain [badDecl] conflict slots goal).isNone

def pairState : CommonRoleSettledConstraints.State 1 where
  atoms := eqs (.pair .int .int)
  child := by
    simp [PresenceGeneratedChildGrammar.GoodAtoms,PresenceGeneratedChildGrammar.GoodAtom,
      eqs,Cycle109Progress.lower,CommonRoleIntervalDictionaryCompilation.lower,
      PresenceGeneratedChildGrammar.lower,PresenceGeneratedChildGrammar.upper]
  width := by
    intro a b h tail ht
    simp only [eqs,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h <;> cases h <;> cases ht
  rows := by
    simp [PresenceSourceConstraintSupport.GoodAtoms,PresenceSourceConstraintSupport.GoodAtom,
      eqs,Cycle109Progress.lower,CommonRoleIntervalDictionaryCompilation.lower,
      PresenceSourceConstraintSupport.simpleTyRows]
def intState : CommonRoleSettledConstraints.State 1 where
  atoms := eqs .int
  child := by simp [PresenceGeneratedChildGrammar.GoodAtoms,PresenceGeneratedChildGrammar.GoodAtom,
      eqs,Cycle109Progress.lower,CommonRoleIntervalDictionaryCompilation.lower,
      PresenceGeneratedChildGrammar.lower,PresenceGeneratedChildGrammar.upper]
  width := by
    intro a b h tail ht
    simp only [eqs,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h <;> cases h <;> cases ht
  rows := by simp [PresenceSourceConstraintSupport.GoodAtoms,PresenceSourceConstraintSupport.GoodAtom,
      eqs,Cycle109Progress.lower,CommonRoleIntervalDictionaryCompilation.lower,
      PresenceSourceConstraintSupport.simpleTyRows]
def empty : CommonRoleSettledConstraints.State 1 := .empty
#guard CommonRoleCheckedOrdinaryReplay.validate empty [pairState,pairState] = true
#guard CommonRoleCheckedOrdinaryReplay.validate empty [intState,intState] = true
#guard CommonRoleCheckedOrdinaryReplay.validate empty [pairState,intState] = false
#guard (runBatches registry slots sources goal empty [empty,pairState,empty,pairState]).map
  (fun r => (r.snapshots.length,r.rebuilds,r.visits)) = some (5,2,3)
#guard (runBatches registry slots sources goal empty [pairState,intState]).isNone
#guard (runBatchGraphs registry slots sources goal empty [pairState,pairState] (fun _ => [])).map
  (fun r => r.2.length) = some 3
#guard (runBatches [badDecl] slots sources goal empty []).isNone
#guard (runBatches [] slots sources goal empty []).map Replay.rebuilds = some 1

example (r : Replay 1) (h : runBatches registry slots sources goal empty [pairState] = some r) :
    r.rebuilds ≤ 5 := by
  obtain ⟨bound,_,_,cost,_,_⟩ := runBatches_computed_bound registry slots sources goal empty [pairState] r h
  exact cost
example (atoms envelope : List (Atom (Fin 1))) (inc : CommonRoleStructuralMaterializationProgress.Included atoms envelope)
    (f : Form) : CommonRoleStructuralOrdinaryMaterialization.materialize atoms slots f ∈
      CommonRoleStructuralMaterializationDomain.variants envelope slots f :=
  CommonRoleStructuralMaterializationDomain.materialize_present inc slots f
end Cycle109Replay
namespace Cycle109Derived
open Yulang CommonRoleCaptureNormalization
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def slot0 : Fin 2 := 0
def slot1 : Fin 2 := 1
def slots (_ : Nat) : Fin 2 := 0
def pair : TyTerm (Fin 2) := .pair (.base .int) (.base .int)
def seeds : List (Atom (Fin 2)) :=
  [.tyLe (.var slot0) (.var slot1),.tyLe (.var slot1) (.var slot0),
   .tyLe (.var slot1) pair,.tyLe pair (.var slot1)]
def initial : CommonRoleSettledConstraints.State 2 where
  atoms := seeds
  child := by
    simp [PresenceGeneratedChildGrammar.GoodAtoms,PresenceGeneratedChildGrammar.GoodAtom,
      seeds,pair,PresenceGeneratedChildGrammar.lower,PresenceGeneratedChildGrammar.upper]
  width := by
    intro a b h tail ht
    simp only [seeds,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h | h | h <;> cases h <;> cases ht
  rows := by
    simp [PresenceSourceConstraintSupport.GoodAtoms,PresenceSourceConstraintSupport.GoodAtom,
      seeds,pair,PresenceSourceConstraintSupport.simpleTyRows]
def decl : CommonRoleStablePaterson.Declaration := ⟨0,0,[.pair .int .int],[]⟩
def registry := [decl]
def sources : CommonRoleGuardedIntervalPlans.Sources := fun _ _ x => x
def goal : CommonRoleIntervalPaterson.Goal := ⟨0,[(.var 0,.var 0)]⟩
#guard CommonRoleStructuralOrdinaryMaterialization.detect seeds slot0 = none
#guard CommonRoleStructuralOrdinaryMaterialization.detect seeds slot1 = some (.pair .int .int)
#guard CommonRoleDerivedStructuralMaterialization.detect seeds slot0 = some (.pair .int .int)
#guard CommonRoleDerivedStructuralMaterialization.detect seeds.reverse slot0 = some (.pair .int .int)
#guard CommonRoleDerivedStructuralMaterialization.detect (seeds ++ seeds) slot0 = some (.pair .int .int)
#guard CommonRoleOpenPropagation.consistent initial = true
#guard (CommonRoleDerivedStructuralMaterialization.run registry slots sources goal initial []).map
  CommonRoleStructuralFrontierReplay.Replay.rebuilds = some 1
#guard (CommonRoleStructuralSaturationTrace.run registry slots sources goal initial).map
  CommonRoleStructuralFrontierReplay.Replay.rebuilds = some 2
#guard (CommonRoleStructuralSaturationTrace.run registry slots sources goal initial).map
  (fun r => r.snapshots.length) = some (1 + (CommonRoleStructuralSaturationTrace.generated seeds).length)
#guard (CommonRoleStructuralSaturationTrace.run [] slots sources goal initial).isSome
#guard CommonRoleStructuralOrdinaryMaterialization.detect
  (CommonRoleStructuralSaturationTrace.finalAtoms seeds) slot0 = some (.pair .int .int)

example : CommonRoleDerivedStructuralMaterialization.DerivedEvidence seeds slot0 (.pair .int .int) := by
  have upper : CommonRoleStructuralCarrierCoverage.Derives seeds (.tyLe (.var slot0) pair) := by
    apply CommonRoleStructuralCarrierCoverage.Derives.trans (.tyLe (.var slot0) (.var slot1))
      (.tyLe (.var slot1) pair) (.tyLe (.var slot0) pair)
    · exact .seed _ (by simp [seeds])
    · exact .seed _ (by simp [seeds])
    · simp [CommonRoleFiniteStructuralClosure.compose]
  have lower : CommonRoleStructuralCarrierCoverage.Derives seeds (.tyLe pair (.var slot0)) := by
    apply CommonRoleStructuralCarrierCoverage.Derives.trans (.tyLe pair (.var slot1))
      (.tyLe (.var slot1) (.var slot0)) (.tyLe pair (.var slot0))
    · exact .seed _ (by simp [seeds])
    · exact .seed _ (by simp [seeds])
    · simp [CommonRoleFiniteStructuralClosure.compose]
  exact ⟨⟨pair,upper,rfl⟩,pair,lower,rfl⟩
example (v : Fin 2 → Comp Common.model) (state : List (Atom (Fin 2)))
    (member : state ∈ seeds :: CommonRoleStructuralSaturationTrace.accumulate seeds
      (CommonRoleStructuralSaturationTrace.generated seeds)) :
    All Common.model v state ↔ All Common.model v seeds :=
  CommonRoleStructuralSaturationTrace.snapshot_models seeds state member v
example (atom : Atom (Fin 2)) : atom ∈ CommonRoleStructuralSaturationTrace.finalAtoms seeds ↔
    CommonRoleStructuralCarrierCoverage.Derives seeds atom := CommonRoleStructuralSaturationTrace.final_membership seeds atom
example (r : CommonRoleStructuralFrontierReplay.Replay 2)
    (computed : CommonRoleStructuralSaturationTrace.run registry slots sources goal initial = some r) :
    r.rebuilds ≤ 5 := by
  obtain ⟨bound,_,_,cost,_,_⟩ := CommonRoleStructuralSaturationTrace.run_computed_bound registry slots sources goal initial r computed
  exact cost

def intState : CommonRoleSettledConstraints.State 2 where
  atoms := [.tyLe (.var slot0) (.base .int),.tyLe (.base .int) (.var slot0)]
  child := by intro a h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
  width := by intro a b h tail ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with h | h <;> cases h <;> cases ht
  rows := by intro a h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
def bad : CommonRoleSettledConstraints.State 2 := CommonRoleCheckedOrdinaryReplay.append initial intState
def invalidDecl : CommonRoleStablePaterson.Declaration := ⟨0,2,[.var 0],[(0,[.var 0])]⟩
#guard CommonRoleOpenPropagation.consistent bad = false
#guard (CommonRoleStructuralSaturationTrace.run registry slots sources goal bad).isNone
#guard (CommonRoleStructuralSaturationTrace.run [invalidDecl] slots sources goal initial).isNone
#guard (CommonRoleStructuralSaturationTrace.run registry slots sources goal (.empty : CommonRoleSettledConstraints.State 2)).map
  (fun r => (r.snapshots.length,r.rebuilds)) = some (1,1)
#guard CommonRoleDerivedStructuralMaterialization.detect
  [.tyLe (.var slot0) (.var slot1),.tyLe (.var slot1) pair] slot0 = none
#guard (CommonRoleStructuralSaturationTrace.runGraphs registry slots sources goal initial (fun _ => [])).map
  (fun output => output.2.length) = some (1 + (CommonRoleStructuralSaturationTrace.generated seeds).length)
example (r : CommonRoleStructuralFrontierReplay.Replay 2)
    (computed : CommonRoleStructuralSaturationTrace.run registry slots sources goal initial = some r) :
    ∃ graphs, CommonRoleStructuralSaturationTrace.runGraphs registry slots sources goal initial (fun _ => []) = some (r,graphs) := by
  obtain ⟨graphs,found,_⟩ := CommonRoleStructuralSaturationTrace.runGraphs_exact registry slots sources goal initial (fun _ => []) r computed
  exact ⟨graphs,found⟩
end Cycle109Derived
```

報告原稿の最終更新: 2026-11-11T05:18:31.031457+00:00。コードはa9955de8から変更していない。
