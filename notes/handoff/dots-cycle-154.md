# Cycle 154: value-supported evidence and historical nominal outputs

B4Bridges V5 の未証明フィールド: **8 / 14**。具体的な Value 境界でも一般の evidenceNode は未完了。

## 時間・復元・範囲

開始 2026-11-13 01:25:00 UTC。最新指示の55分上限を優先し、02:20:00 UTCより前に公開・照合まで終える。
前153の completed 心拍・報告と公開head `9ad62614f69b490820b8295f9a981a897ccfbf48` を確認。
前writer/buildなし。新規の独立worktreeを使い、既存のLean cacheはコピーせず一つを共有。
開始時空き40 GiB。使用量枠は不明。

`integration/m1-final` は今回APIで `c10b05194d3b3d439994a6a3dc0470a4e8a5776c` を取得し直し、
standing orders・inboxを再読。ACTIVE、STOPなし。I-25とI-24の新追記（新moduleはYulang.leanからimport）に従う。
新integrationのvalue-provenance層を変更せず取り込み、公開merge commitの第2親として保持した。
Astra所有のStep/Stable/Generated/target定義は変更していない。公開先はwork/dots-mainのみ。

## 完了済みの部分目標

1. **過去の有限観測から、任意の実feedback/reobservation/value trace後の制約を導く。**
   固定request batchのschemaはconstructorsとinterpretationにしか依存しない。
   実stepはその二つを保ち、同じ最終modelを過去へ戻せるので、最終のmaterialization Modelsが成り立つ。
   前153の「normalized view全体が不変」という制限を、意味的な結論について除いた。
   現在の構文的Observedが保存される、とは述べていない。
2. **新しいValue安定性を実際に使う条件付きnode健全性。**
   selectedから強いDecisionGuardを取り出し、実際に有効なPacketGuardを構築。
   Jointとmerge closureがあればStableからCommittedを得て、全最終modelのInstanceとfull Evidenceを得る。
   reachableならmerge closureは導出できる。packet-free reachableではJointも除去。
   旧境界のStableを仮定する置き換えはしていない。
3. **historicalな出力観測を使う現在のselected branchとfull node Evidence。**
   現在のnominal head Shapeと、過去snapshotにおける最終request batchの有限Observedを仮定し、
   任意の実Value trace後の現在Instance/BranchAt、同じ最終modelの子辞書から親Evidenceを構成。
   この構造的な経路ではJoint/Stableは不要。ただしShape/Observedを全reachable状態から導く橋は未完了。
4. **三引数nominal named-outputの非空・安定・分類・辞書の具体例。**
   checkedな宣言、実named-output request、InitialSource、具体的なmodel、初期Reachableを証明。
   最新Value境界でStableと厳密なClassify(selected node)を示し、全modelでfull Evidenceを得た。
   三つのprojection pathを別々に検査し、前のbinary certificateでは表せないことも証明。
   **terminalで、出力が初期状態ですでに観測済みのzero-step実行**である。
   install/merge/refresh後の成功例と取り違えない。

5. **nonterminalの実installを含む成功例も完了。**
   同じ二slotのsourceで親headを`N(a,b,c)`、子を`Display a`とし、三引数nominal named-outputを保持。
   初期状態はnot_stable、実Value installがchild edgeと非空journalを作る。
   最終payloadは`.node 155 [.node 3 []]`。到達性・非空model・Stable・厳密な再帰Classify・全最終modelのfull Evidenceを
   一つの無前提定理`value_installed_stable_classified_dictionary`に束ねた。
   出力先は既存観測slotであり、新規割当ではない。merge/refreshはこの実行列にはない。
6. **記録packetから、初期にtarget slotがなくても出力制約を回収。**
   実Value到達履歴から、全retained packetのschema coherenceとRequestReady由来のunknown=falseを導いた。
   任意の記録request subsetはそのtestを保持し、variables=[]なら任意の現在report/captureでModelsが成立。
   rootRequestsの包含は自動。初期Observedやtarget-slot witnessは不要。
   これはmaterialization結果であり、一般の現在Instanceや最終model存在を導くものではない。
7. **reserved出力の適用境界を具体化。**
   reserved identity 2は初期sourceに属するがcarrier slotを持たず、Observedは不成立。
   InitialSource/Reachableを満たす非空source modelで出力2=intを選べば三引数nominal要求を満たさない。
   したがって、初期から全modelが出力制約を満たすと置く証明はこの入力には適用できない。
   さらにtarget2をnominalにする別のpositive modelを構成し、実Value installを証明。noveltyはint2反例で示す。
   到達性・非空最終model・記録packetを回収し、一般recorded theoremを適用して任意final modelの出力Modelsを得た。
   reserved identityはこの例の初期入力であって、transitionで新規割当したとは述べない。このvariantのStable/Classifyも未主張。

## 新しい定理の名前・主張・側

正確な量化子・前提は[全201定理の型](dots-cycle-154-types.md)に記録。
すべて健全性またはその補助であり、完全性・主型性の完成とは数えない。

| Module | 定理群の主張（明示した全入力・前提の下で） |
|---|---|
| HistoricalRequestModels | `generated_eq`・`extension_generated`・`at_generated`・`trace_generated`: 固定requestのschema不変。`generated_models_after_trace`・`generated_shape_after_trace`・`actual_requests_models_after_trace`: 過去の有限点木観測から、任意feedback trace後の各最終modelの制約と閉じたschemaを導出。最後はvariable-only where条件付き。 |
| ValueEvidence | `stable_site`・`selected_support`・`stable_joint_packet`: 実guardと有効packetを回収。`stable_joint_instance`・`stable_joint_evidence`: Joint等から全model Instanceと子辞書付きEvidence。`stable_merges_of_exact`・`reachable_joint_instance`・`reachable_joint_evidence`: reachable exact ledgerでmerge条件を除去。`steps_reobservation`・`reachable_reobservation`: 実trace/到達性の正しい向きの消去。`reachable_packetFree_terminal`・`reachable_packetFree_evidence`: packet-free条件下でJointなしのterminal辞書。 |
| HistoricalValueRequests | `at_generated`・`trace_generated`・`generated_models_after_trace`・`generated_shape_after_trace`: descriptor reobservationも含む意味保存。`value_generated_models`・`value_generated_shape`: 実Value traceに適用。 |
| HistoricalTreeBranch | `branch_models`・`ready`・`instance_of_shape`・`selected_instance`・`selected_branch`: 現head Shape＋過去出力Observedから現在branch。`value_selected_branch`・`value_node_evidence`: 実Value traceの最終modelでBranchAt/子辞書から親full Evidence。 |
| FiniteObservedExample | `state_models`・`translation`・`observed`・`tests_exact`・`every_source_model`・`inhabited_request_models`: 三引数出力の実観測と全model制約。`no_closed_tree`・`not_closed_observed`: binary上限では表現不能。`checked`・`registry_checked`・`metadata`・`initial_source`: 実宣言/初期状態の条件。`named_request_present`・`actual_requests_exact`・`actual_request_models`・`report_exact`・`branch_models`・`ready`・`actual_instance`・`full_evidence`・`actual_reachable`・`reachable_inhabited_named_evidence`: 実named-output入口と非空の辞書。 |
| FiniteObservedExampleStable | `initial_models`・`generated_root`・`installs_committed`・`varying_source`・`refresh_large_unknown`・`point_closed`・`feedback_stable`・`stable`・`stable_reachable_named_dictionary`: 全ての実update候補を排除して初期状態が安定、各modelで辞書。 |
| FiniteObservedExampleClassify | `no_root`・`no_candidate`・`root_ready`・`prepared`・`children_empty`・`survivor`・`unique`・`selected`・`decisions`・`support_selected`・`classified`・`stable_classified_named_dictionary`: K2/保留の排除と厳密な分類。`value_selected`・`value_stable`・`value_reachable`・`value_classified`・`value_stable_classified_named_dictionary`: 最新Value境界へ適用。 |

### 追加の定理群

- `FiniteObservedExampleNonterminal*` 8module（74公開定理）:
  `checked`・`registry_checked`・`initial_source`・`initial_models`から実sourceを構成し、
  `prepared`・`survivor`・`initial_joint`・`selected`・`guard`・`enabled`で実installの全条件を導く。
  `novel`・`not_stable`・`value_install_step`で非zero stepを示す。
  `installed_models_iff`・`final_parent_instance`・`final_child_instance`・`final_evidence`は各最終modelでの辞書。
  `feedback_stable`・`stable`・`value_stable`・`value_classified`を経て
  `value_installed_stable_classified_dictionary`で実行・分類・辞書を一括。
  全ての名前と前提は型付録に列挙。
- `RecordedRequestModels` 12公開定理:
  `subset_tests`・`coherent_at`・`coherent_trace`・`reachable_coherent`で記録schemaの実履歴を証明。
  `recorded_variableFree_models`・`reachable_root_requests`で現在の任意reportへの制約を回収。
  `subset_known`・`requestsKnown_at`・`requestsKnown_trace`・`reachable_requestsKnown`・
  `reachable_subset_known`・`reachable_root_closed`でunknown=falseを履歴から導出。
  variables=[]は残る。`SchemaCoherent`・`RequestsKnown`は結論の仮定ではなく実到達性から導出した不変条件。
- `FiniteObservedExampleReserved` 9公開定理:
  `reserved_source`・`no_target_slot`・`not_observed`で観測の限界、
  `source_models`・`actual_requests_exact`・`initial_source`・`initial_reachable`・`tests_exact`・
  `initial_countermodel`で非空の実初期状態から制約未充足を証明。

- `FiniteObservedExampleReservedPositive` / `ReservedRecorded` 26公開定理:
  `positive_source`・`positive_request`から有効なPrepared/selected/Joint/guardを構成。
  `novel`・`value_install_step`・`installed_models`・`value_reachable`・`packet_recorded`・`journal_nonempty`を証明。
  `recorded_request_models`は任意capture/report・任意最終modelへ一般定理を実適用。
  `reserved_install_regression`で無slot、非Observed、実step、到達性、非空model、全最終model制約を一括。

## 検証

[検証ログ全文](dots-cycle-154-validation.md)。focused `lake build ... --wfail`: **762 jobs、exit 0**。
新しい監査shard計203項目（201公開定理＋2不変条件定義）をすべて`lake env lean --trust=0`で実行。定理と不変条件定義を検査。
全新moduleの全宣言（定義・private・生成宣言を含む）依存gate: **19 module / 444 declarations、PASS**。標準3公理のみ。
`verify-lean.sh . c10b05194 --no-build`: **PASS**。これは差分gateだけで、全体build/全体auditではない。
新moduleのYulang.lean importあり。Audit.lean、README、lake設定、spec、planは編集していない。
全体検証はstanding ordersにより実行せず、監督役に残す。

独立レビューで、fixtureの非空性・seed/source/未割当・Metadata・Value安定性の変換方向、
historical結果の同一model使用を点検し、重大な問題は見つからなかった。

## Yulang2・失敗・制限

既存x-oracleの関連型/nominal事例を参照。新しいYulang2実機・parser照合は行っていない。
今回のfixtureは既存Lean定義の具体化であり、ソース言語全体との挙動一致とは主張しない。
初期の実行PATHにlakeがなく、既存Lean4.35.0実行器を明示して解消した。
開発中のconstructor patternと一時gateの型エラーは修正後に再検証済み。
最後の差分gateは未commitのYulang.lean importを検出して一度FAILした。importをcommit後に再実行しPASS。
一度local git検査が不必要なgithub通信として拒否されたため、遅延fetchを無効にしたlocal-only検査に分けて成功した。
権限を回避した外部書き込みは行っていない。

公開checkpointのCI status APIは空、workflow APIもPRイベント限定の空結果であり、CI PASSとは主張しない。
一般alias coverage、非empty journalの一般Joint、fresh request coverage、現在head Shapeの一般導出は未完了。

## 境界13項目の棚卸し

| 項目 | 状態 |
|---|---|
| Checked | 一般nominal定義あり。言語全体忠実性は別。 |
| Models | 一般定義あり。 |
| RootPending | 一般定義あり。 |
| RootK2 | 一般定義あり。 |
| CandidateK2 | 一般定義あり。 |
| InspectionPending | 一般定義あり。Value supportの保留も含む。 |
| Survivor | 一般nominal候補定義あり。 |
| Reorders | 一般定義あり。 |
| DictionaryEquivalent | 一般定義あり。 |
| Step | Astraの一般定義あり。変更なし。 |
| Stable | 一般定義あり。変更なし。 |
| Generated | 一般定義あり。変更なし。 |
| Evidence | 一般定義あり。一般evidenceNodeは未完了。 |

未証明8項目: progress, execution, halted, whereAccessible, treeExecution,
canonicalLocalOrder, evidenceNode, generatedChildren。

## 公開checkpoint

- `41e8858af4905d6b78782aac86e6f52eaefc77de`: 最初の2module。7source paths byte-readback、tree照合済み。
- `45d106b01cb3f6a100dc7332feb142916a7f253c`: 7moduleの検証済みcheckpoint。12source paths byte-readback済み。
- `190022fcaa9acd9c181429a2d3ada2225ee5eee0`: nonterminal実install。全12path byte-readback、tree照合済み。
- `a38b15eb75cd584868c5f595a4c5aec45571c59f`: recorded request transport。全5path byte-readback済み。
- 開始・約10分・約20分・約30分・約40分の心拍を公開済み。すべてnon-force expected-head更新。

## 次の候補

1. 今回のreserved実install後に現在Instance/Stable/Classifyをつなぐ。さらに真のfresh allocation traceへ拡張。
2. historical request batchをfresh source generationから導き、固定batch条件を縮める。
3. Value到達状態から現在head Shape/alias coverageを導いて一般evidenceNodeへ接続。

## 完了記録

2026-11-13 02:12 UTC、実作業開始から47.8分で検証と報告を確定。
成果commit `f64ae016091bf2778ec483171cf9b0ad2e4ff536` の40変更pathを、immutable refから全文byte-readbackして一致確認。
19新module / 201公開定理。focused build 762 jobs、trust0監査203項目、全444宣言依存gate、commit済み差分gateはPASS。
終了時空き40 GiB。ビルドと補助workerは終了し、writerを解放。心拍はcompletedへ更新。
一般V5残数は8/14のままで、未完部分を完成扱いしない。
