# dot cycle143 — support-aware V5 辞書橋

## 復元・範囲

- scheduled run: 2026-11-12T14:27:19Z。実際の起動記録は14:24:04Z。時刻を遡って丸めない。
- fresh `integration/m1-final`: `6cff680ccafc24ab298e1b890adcb6d7bba15034`。
- 前回公開: `f733a48d3421d831af6eb404c89be7944373670c`、cycle142 completed。前writer/buildなしを確認。
- standing orders / inboxを再読。I-25継続、STOPなし。新しいsupport-aware boundaryが統合されていたため、この実際の境界でEvidenceを扱った。
- 最新55分上限を優先。Astra所有のStep/Stable/Generated等の定義、凍結Audit.lean/README.mdには変更なし。
- integrationをlocalへmergeした際のYulang.lean import競合は、既存importとAstra追加9importを全て保持して解決。

## 主成果

一般V5が完成したとは主張しない。support-aware Reachableの上で、従来別に要求していたmerge closureを実際のStableから導いた。非空journalの一般Evidenceに残る適用条件はJointであり、同じ最終モデルの子Evidenceと組み合わせて親Evidenceを作る。packet-free reachableではJointも除去し、選択された辞書がterminalであることまで証明した。

Jointは局所survivorの別名ではない。全aliased packetのkey一致と、focusおよび同じalias群の全siteのBranchAtを、関連型の全出力義務込みで同時に満たす単一journalモデルを要求する。

### SupportEvidence

任意roles/registry/実tracked state/rootについて:
- `steps_old`, `reachable_old`: 実support trace/reachabilityを旧reobservation関係へ写す。support Stableを旧Stableへ写すことはしない。
- `stable_site`, `selected_support`: 実support Stableとlinked rootから記録site、実selectedからDecisionGuardの有限supportを得る。
- `stable_joint_packet`, `stable_joint_instance`, `stable_joint_evidence`: Stable・selected・Joint・recovered merge closureから、現在contextのinstallableかつcommitted packet、任意最終モデルのInstance、同一モデルの子Evidenceを使った親Evidenceを構成する。
- `slice_pool`, `related_known`, `recovered_endpoint`, `merge_guard_of_exact`, `stable_merges_of_exact`: source形成のExactから全dependencyPoolのSlice=Modelsを導き、実MergeGuardとalias closureを構成する。現在のMergeGuardにAdmissible条件はない。PacketGuardには別途正当なadmissible supportを構成しており、両者を混同しない。
- `reachable_joint_instance`, `reachable_joint_evidence`: 任意の実reachable stateで上記merge条件を消去。残余はJointと同じ最終モデルの子Evidence。
- `reachable_packetFree_shape`, `reachable_packetFree_joint`, `reachable_packetFree_terminal`, `reachable_packetFree_evidence`, `nonterminal_has_packet`: 実reachableでpacket listが空ならsitesはroot単独、edgesは空。rootまたはgenerated focusの選択でJointが得られ、Stableならchildren=[]、任意最終モデルでterminal Evidence。逆に非terminal選択ならpacketが存在する。

### SupportJournal / SupportChoices

任意の実SourceFormed support stateとその記録packetについて、元のpacket.contextにおけるInstance、正確なemitted edgesを含むCommitted、source registryとの一致、宣言のvisibilityを保つ。`recorded_evidence`は**そのpacketの保存context**の同一モデル子Evidenceを要求する。現在contextや他packetのcontextへ勝手に移さない。

singleton registryでは全記録key一致を証明し、Jointのkey半分を消去した。同時モデルの存在は明示的残余のまま。

`SupportChoices.Coherent`はaliasされた記録packetのkey一致。実administrative更新とenabled installはこれを保存する。実SourceFormedかつ**最終alias listが空**なら途中mergeを排除でき、Coherentが得られる。記録されたkeyはそのalias class全体を決める。さらに`alias_merge_cases`で一つのmerge後のaliasを旧同値類内/二旧同値類の交差へ分解し、`merge_coherent_iff`で「merge後Coherent iff 旧Coherentかつ二旧class間の全packet key一致」を証明した。SameInputs/MergeGuardから交差key一致を導いたとは言わない。`formed_coherent_of_merge_keys`は実SourceFormed traceの各enabled mergeにだけこの局所交差key条件を課し、他の全stepの保存を合成する。

### SupportTree / SupportComposition

任意の固定reachable snapshot、root Stable、実Classify selected dictionaryについて、辞書のsizeによる相互再帰で同一最終モデルのEvidenceを構成する。Jointは、そのsnapshotがモデルを持つ場合のselected Generated nodeにだけ要求する。全stateのEvidenceNodeを仮定しない。packet-freeではJointなしで辞書健全性と単一terminal node形状を証明する。

実support boundaryと既存の非計算的executorについて、次の**4残余**を明示してV5 Statementへ合成した:
1. Progress（実reachable更新の整礎性）
2. where-child accessibility
3. executor最終stateのcanonical local order
4. stable selected generated nodeのJoint

EvidenceNode/GeneratedChildrenという結論そのものを仮定する代わりに、4の意味論的残余からそれらを構成する。Progressを仮定したexecution/halted/treeExecutionを無条件の成果に数えない。GeneratedChildrenはモデル引数を持たないため、全体のJoint残余をモデルありの場合だけに弱めたとは言わない。

### 正例と、主張の境界を検証する反例

- `SupportForkExample`: 実initial sourceからpoint/wide refresh、wide→pointのCertified revision。sourceの未知head0はsource entailmentから正当に回復され、reads=[0,2,3]、空producer supportでDecisionGuard。pointは実reachable・Stable・selected90[]・packet-free・モデルありでterminal Evidence。wideはrevisionが可能なので非Stable。実V5 ClassifyとResolvesも証明し、新しいgeneric Classify-to-Evidence定理を具体例に適用した。
- `SupportNonemptyExample`: 実initialからPacketGuard付きterminal output install、実scalar refresh。PointClosedで追加reobservationを排除し、実reachable・Stable・**非空journal**・明示的model・全最終モデルのcurrent Instance/Evidenceを証明。意味論的Evidenceは保存contextへの逃避でなく現在contextで再検査している。
- `SupportRecursiveExample`: 既存registryのDisplay key1とInt key3を再利用。実guarded parent installから非空journalへ到達し、**全最終モデルで同一final contextの完全な再帰辞書 `.node 1 [.node 3 []]` のEvidence**を証明。実model存在も示す。子はterminalなので架空の2回目installを作っていない。Stable/Classifyは主張しない。
- `SupportRevisionObstruction`: 実initial→guarded install→問い合わせslotのCertified point revision。Modelsと非空journalを持つ実reachable stateで¬Current。その**同じstate**でhistorical Instanceは保たれる。Stableは主張しておらず、V5 Evidenceの反証ではない。
- `SupportCompletionGap`: 実source-supported installで到達するモデルあり・非空journalでもContextCompleteは導けない。rawの候補モデルをjournalモデルへ無条件に持ち上げる近道を排除する。Stable/selectedの反例ではない。
- `SupportInhabitation`: ordinary int≤strを含む実InitialSource/ReachableでModelsが空。InitialSourceには非空性仮定がなく、その代わりにEvidenceのvalid modelを他フィールドへ流用できない。これもV5の反証ではない。

## 13項目と橋の状況

「一般定義あり」は現在のgeneral nominal carrierでの定義を指す。言語全域のparser/inference/elaboration網羅性や全体主定理の完成を意味しない。

| SourceBoundary項目 | 状態 | 現在の具体化と制限 |
|---|---|---|
| Checked | 一般定義あり | GeneralDeclarations。全言語producer接続は別 |
| Models | 一般定義あり | tracked.currentのsource+packet+site意味論、Exact ledger |
| Step | 一般定義あり | support guard付きinstall/mergeと実administrative更新 |
| Stable | 一般定義あり | 同じ実Stepの閉性。一般停止証明は未完成 |
| Generated | 一般定義あり | 実emitted edgesとalias閉包 |
| RootPending | 一般定義あり | source lower-head保留 |
| RootK2 | 一般定義あり | source/feedbackの循環判定 |
| CandidateK2 | 一般定義あり | candidate inspectionの循環 |
| InspectionPending | 一般定義あり | 従来pendingとSupportPending |
| Survivor | 一般定義あり | 現在raw-context候補。Jointとは別 |
| Evidence | 一般定義あり | source occurrence索引・同一モデルの再帰Evidence。一般橋はJoint残余 |
| Reorders | 一般定義あり | source registry reordering |
| DictionaryEquivalent | 一般定義あり | payload/source対応に基づく既存比較 |

無条件のV5橋は6/14、未証明8/14のまま:
`progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder, evidenceNode, generatedChildren`。
閉じた6本は`closure, stepModels, frontierLocal, localIdentity, dictionaryRefl, initialReorders`。
今回の条件付き合成は未証明数を減らしたとは数えず、依存する残余を4本に整理した。

## 次の具体的な義務

1. 実reachable・Stable・selectedの非空alias classで、Jointのkey一致と単一同時モデルを導く。local survivorの一意性だけを使わない。singleton/alias-freeの今回の補題は一般mergeを覆わない。
2. historical packetの観測とcurrent branchの意味論的対応を、保存childrenの構文的同一性から分ける。¬CurrentをV5反例にすり替えない。
3. AstraのProgress/accessibility/canonical-order作業とは定義を衝突させず、現在4残余のうち辞書側Jointだけを狙う。

新しい言語意味論を決定せず、質問ノートは追加していない。既存specの同入力併合と自己出力由来展開の保留を読み直した。

## 検証・公開・制限

新規11モジュール、公開theorem 103本を追加。全103本を小さな`Audit/Cycle143.lean`で監査した。使用量枠は不明。

- 全11対象への`lake build --wfail`成功、747 jobs。
- `lake env lean --trust=0 Audit/Cycle143.lean`成功。103件のaxiom出力を機械検査し、使用axiomは`propext`, `Classical.choice`, `Quot.sound`のみ。sorry/new axiom/native_decideなし。
- `git diff --check`成功。
- 全体`lake build`や凍結`Audit.lean`の全監査は実行していない。個別対象の推移的依存だけをbuildした。新しいYulang2 runtime oracleは実行していない。
- 独立reviewでsupport→旧関係の向き、保存context/current contextの区別、Jointの量化、反例の非空性、非空terminal/recursive Evidenceと最終モデルの同一性、merge key iffを確認。最後のtrace合成とclassified harnessは追加後に再build/監査した。
- 無条件V5橋の完了数は変更なし。具体例を一般ProgressやJointの証明に数えない。

公開は`work/dots-main`のみ、expected SHA付き非force更新。integrationブランチには書き込んでいない。Git blobの個別作成要求を使わずinline treeで公開した。

途中公開:
1. `b1d2e32962e06fb5e4f6baf08e2d7535b725560d`: 初期32宣言とfresh upstreamを保持、19 files readback一致。
2. `5e9746e7c3c7735050fd72505244e7e29c3e8130`: 66宣言、9 changed files一致。
3. `f00debcb1a4eb656cf8b398880bc1b08136e4190`: 84宣言、6 changed files一致。
4. `487985c3b6eda93a46f5b2c94cebbad875853f45`: 最終103宣言、6 changed files一致。最終reviewでmutual内2定理の報告一覧漏れを修正。監査には元から含まれており、重複追加を除いてunique103件で再実行。ソース14ファイルの再取得はこの時点で全一致。最終report/audit/guide更新後にも再照合する。

最終source local commit: `188c55b14`。以下は省略なしのno-build gate出力。これはbuildの代替ではなく、上記focused buildと別に実施した。

```text
verify-lean: . @ 188c55b14 (base origin/integration/m1-final)
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

## 公開定理一覧

各定理の量化・条件は上のグループ説明および実Lean statementを参照。private helpersは依存証明として監査対象に入るが、この103本には数えない。


### GeneralDictionarySupportChoices (8)

`administrative_coherent`, `install_coherent`, `formed_aliasFree_coherent`, `recorded_class_key`, `alias_merge_cases`, `merge_coherent`, `merge_coherent_iff`, `formed_coherent_of_merge_keys`

### GeneralDictionarySupportCompletionGap (8)

`source_decision`, `packet_guard`, `actual_step`, `actual_reachable`, `actual_inhabited`, `actual_nonempty`, `context_incomplete`, `no_reachable_context_complete`

### GeneralDictionarySupportComposition (4)

`evidenceNode`, `generatedChildren`, `bridges`, `statement`

### GeneralDictionarySupportEvidence (19)

`steps_old`, `reachable_old`, `stable_site`, `selected_support`, `stable_joint_packet`, `stable_joint_instance`, `stable_joint_evidence`, `reachable_packetFree_shape`, `reachable_packetFree_joint`, `reachable_packetFree_terminal`, `reachable_packetFree_evidence`, `nonterminal_has_packet`, `slice_pool`, `related_known`, `recovered_endpoint`, `merge_guard_of_exact`, `stable_merges_of_exact`, `reachable_joint_instance`, `reachable_joint_evidence`

### GeneralDictionarySupportForkExample (12)

`refresh_step`, `repair_step`, `reachable`, `point_stable`, `wide_not_stable`, `decisions`, `point_selected`, `terminal_evidence`, `inhabited_terminal`, `point_classified`, `point_resolves`, `classified_dictionary_sound`

### GeneralDictionarySupportInhabitation (5)

`raw_no_models`, `initial_source`, `actual_reachable`, `no_models`, `source_formation_does_not_imply_inhabited`

### GeneralDictionarySupportJournal (7)

`recorded_instances`, `packet_registry`, `recorded_evidence`, `packet_visible`, `singleton_choices`, `singleton_joint`, `recorded_committed`

### GeneralDictionarySupportNonemptyExample (13)

`decisions`, `packet_guard`, `install_step`, `refresh_step`, `actual_path`, `reachable`, `point_closed`, `stable`, `nonempty`, `inhabited`, `current_instance`, `current_evidence`, `completed`

### GeneralDictionarySupportRecursiveExample (12)

`children_exact`, `enabled`, `actual_step`, `initial_source`, `actual_reachable`, `parent_instance`, `leaf_instance`, `final_leaf_evidence`, `final_recursive_evidence`, `nonempty_journal`, `final_inhabited`, `nonvacuous_recursive_dictionary`

### GeneralDictionarySupportRevisionObstruction (10)

`decisions`, `packet_guard`, `installation`, `revision_step`, `actual_path`, `reachable`, `modeled_nonempty`, `not_current`, `reachable_current_failure`, `historical_but_not_current`

### GeneralDictionarySupportTree (5)

`classified_evidence`, `classified_children_evidence`, `snapshot_dictionary_sound`, `packetFree_dictionary_sound`, `packetFree_classified_terminal`

## 次サイクル向け分解の追加

再帰正例のClassifyとStableは別に進められる。current parent/leaf Localを再構成すれば2-node Classifyへ進める一方、Stableには全generated focusのinstallable→Committed、root/child SameInputs否定、ContextComplete、予約originのcertified refresh排除が必要。PointClosedだけでは最後のrefresh義務を覆わない。詳細な未証明の型・分解をmodule guideへ記録した。

## 保全と公開ファイル数

今回の独自成果はLeanモジュール11、aggregate import1、小監査1、module guide1、報告1、heartbeat1の計16パス。前work headに対してfresh integration由来13パスもそのまま保持し、aggregateを除く上流13ファイルはintegration commitとのbyte一致を追加検査した。総変更は29パス。定理のソース集合・auditのunique集合・報告一覧の集合が103本で完全一致することも検査した。

中断なし。14:38の途中heartbeatでupdatedを誤って14:44と記載したが、直後に実時刻14:38:05へ修正し、研究結果には影響なし。review時にmutual定理の一覧漏れと件数の一時的誤認があったが、最終はunique103本で一致し、監査重複も除いた。

最終公開バッチ準備: 2026-11-12T15:12:55.799286+00:00、実開始から48.9分。公開・再取得照合・親への報告を残す。55分上限の保守的期限は15:19:04Z（scheduled基準なら15:22:19Z）。

最終検証記録: 2026-11-12T15:13:58.349624+00:00、49.9分。報告・guideは`6a09c76a70f83c2d96296f1cd295c954bfeeae32`で公開し、3変更パスを完全再取得一致。さらに全ソース・監査・aggregate・guideの14パスを同じ公開commitで再取得し全一致。completed heartbeatとこの記録を最終反映して終了する。実行中buildなし、writerを解放する。
