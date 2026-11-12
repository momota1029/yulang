# Cycle138: raw安定journalのEvidenceNode反証と、到達可能な辞書の正例

開始 2026-11-12T09:27:19Z。ユーザーの55分上限: 10:22:19Z。
最新取得integration: `88d8ba0fa0d8670b39bcf4f9ad6a8a2cc5125063`。
standing orders/inboxを再読しI-24を確認。09:46頃にも同じintegrationと文書blobを再取得。
前137は完了・公開済み・writer解放済み。前回と並行書込みなし。

## 最重要結果

`GeneralDictionaryRefreshGap.no_evidenceNode` は、既存の定義を一切変えず、
`B4SkeletonV4.EvidenceNode (GeneralDictionaryFeedbackEvidence.boundary roles)`
を**否定**した。ここでrolesは既存回帰例の具体的なrole環境。
実際のStable・実際のselected40[]・検査済みregistry・具体的なjournalモデルを使う。
子は空なので子Stable/子Evidenceの前提は正当に成立する。

可視キー40のterminal辞書は関連出力intを要求するが、同identityの不可視な古いキー41の
packetは出力を要求しない。journalに残るstringモデルでは親Evidenceが偽である。
古いキーが新しいinstallationを止め、singleton sitesがenqueue/mergeを止め、
journalとrawモデルの一致が新しいequateを止める。さらにintモデルとstringモデルの
**両方**を保存する任意のexact Refreshでは、source1をKnownにできないことを証明した。
これは固定viewだけのrefreshを除いた疑似Stableではなく、実Atの全5規則に対するStable。

同時に`not_sourceFormed`を証明。**初期化から到達可能な状態やYulang言語全体の反証ではない。**
現状のraw全状態を量化するproof-interfaceが強すぎることを特定した。
`no_bridges`より、この具体的boundaryではどのexecutor/frontiersを選んでも既存の
B4Bridges13フィールド全部を満たせない。B4Statement自体の別経路による否定は主張しない。
Astraの定義やtargetを勝手に弱めていない。修復層の判断は質問ノートへ記録した。

## 独立して進めた正の成果

1. 任意のregistry/root/contextについて、空journalから実際のordinary更新と
   同一carrier・同一viewの認証refreshを混ぜた有限traceに沿い、**最終journalの全packet**の
   Instanceを最終contextで得る。各packetの旧context→最終contextの普通のExtensionは不要。
   前137の混合trace運搬を土台とし、今回の新規部分は全記録に一様な初期不変量である。
2. 実際のinstallationとdescriptor-changing refreshを持つ非空モデル例で、旧packetから
   最終contextへの普通のExtensionが偽でも現在Instanceは成立する。子はK2拒否なので
   この例だけから完全な親辞書ができるとは言わない。
3. 純粋な記録網羅性Coveredと全記録子辺のAccから、順序と重複を保った有限Dictionaryを
   構成する。意味的Evidenceや完成済みの木を前提にしていない。実初期traceを加えると、
   **同じ一つの木**が全最終モデルで現在contextのEvidenceとなる。
   Coveredはexact occurrence一致、Accは代替packetを含む全辺に対する前提。
   Stable/selectedからこの2条件が一般に得られるとは証明していない。
4. terminal40の関連出力例を、旧saturationだけでなく**実feedback installation**で実行。
   Covered/Accを具体的に証明し、有限辞書を生成。実モデルが残り、旧string反例が排除される。
   InitialSourceとSourceFormedも証明した。ここまででStable完了は主張していない。
5. SourceFormedの構造帰納法により、任意の記録packetの宣言がregistry可視であることを
   **Modelsの存在を仮定せず**証明。singleton registryでは全packetのキーが実際のselectedキーと
   一致する。一般registryのhistorical-to-current applicabilityと、alias全体の同時BranchAt
   witnessは残るため、SourceFormed版EvidenceNodeが完成したとは言わない。
6. 別の非空raw例ではStable/selected/¬Jointと**正しい現在Evidence**が同時に成立する。
   `ModeledSelectedJoint`という十分条件も一般には偽で、Evidenceの必要条件でもない。
   この例と、実際にEvidenceが偽のキー40/41反例を区別した。

7. 正例をさらに実際の**view-changing exact refresh**で進め、SourceFormed・実Stable・
   非空モデル・全最終モデルにおける現在Evidence40[]を同時に証明した。
   関連出力方程式からsource1のscalar観察を認証する。予約sourceが全てKnownだと仮定せず、
   任意のn≥2についてint/stringを変える実モデルを作り、将来のexact refreshが新しいKnownを
   作れないことを示す。ContextCompleteでequate、任意のenabled packetのCommittedで
   再installationを閉じた。現在Evidenceは新query/schemaから直接再構成し、固定viewの
   transportを誤用していない。中間の`completed`は最終Localを含まなかったが、続く`resolved`では実Local selected40[]も証明。
   無変更boundaryのLocalへの対応とClassify(.node40[])まで確認した。これは具体例の解決であって、
   一般executor・一般停止性・raw EvidenceNodeの修復ではない。

8. 任意registryについて、現在Instanceと**同一occurrence**の実selectedからキーと順序付き子列の
   一致を証明。選択が供給する共通Linked/Fresh/非Pendingと、Instance固有のbranchからSurvivorを
   構成するため、追加Fresh/Joint前提はない。実restricted初期traceの記録へ接続した。aliasへの
   運搬や全SourceFormedについての一般化は主張しない。

分類: 健全性の構成部品、条件付き有限readback、具体的正例、proof-interfaceの形式的反例。
一般完全性・原理性・全言語の決定可能性・構文からのadequacyは証明していない。

## inbox受け入れ条件との対応

- I-21/I-23の一般evidenceNode閉鎖は**未達**。既存Evidenceを弱めず、現raw feedback境界の義務は
  実際に偽と証明した。SourceFormed限定の一般版を完成済みとはしない。
- I-21の辞書部品の接続は前進: 現在journal不変量、条件付き有限tree、実selectedとの一般同一occurrence整合性。
  具体的な正例では実初期化・2更新・安定・選択・診断・全モデルEvidenceまで接続。
- I-22のK2順序を変更していない。descriptor変更例の拒否された子に完全辞書を主張しない。
- I-24は達成: 巨大Audit/READMEは凍結、6小監査と新module guide、Yulang importだけ追記。
- Astra担当の宣言/候補/Step/Stable/Generatedは一切変更しない。

## SourceBoundary 13項目

一般の定義ありは全言語の網羅性やB4の証明済みを意味しない。

| 項目 | 状態・制限 |
|---|---|
| Checked | 一般の定義あり。既存の検査済みregistry |
| Models | 一般の定義あり。実際のjournal/source models |
| RootPending | 一般の定義あり。source observationは保守的 |
| RootK2 | 一般の定義あり。実feedback/cycle述語を使用 |
| CandidateK2 | 一般の定義あり。実feedback/cycle述語を使用 |
| InspectionPending | 一般の定義あり。未対応inspection/materializationはpending |
| Survivor | 一般の定義あり。source compilation全体の完全性は未証明 |
| Reorders | 一般の定義あり。既存のvisible/where順序関係 |
| DictionaryEquivalent | 一般の定義あり。既存payload同値 |
| Step | 一般の定義あり。Astraの実feedback更新を無変更で使用 |
| Stable | 一般の定義あり。実no-step安定性を無変更で使用 |
| Generated | 一般の定義あり。実際の生成closure |
| Evidence | 一般の独立定義あり。条件付き現在journal健全性と有限辞書構成を追加。raw全安定状態のnode橋は反証済み |

## B4SkeletonV4: 未達成8/13 = 未解決7 + raw境界で反証済み1

| フィールド | 状態 |
|---|---|
| progress | OPEN。一般installation descent未証明 |
| execution | OPEN。完全な一般executorなし |
| halted | OPEN |
| closure | 実feedback boundaryで上流証明済み |
| stepModels | 同boundaryで上流証明済み |
| frontierLocal | 実非計算的frontierで上流証明済み |
| localIdentity | 同frontierで上流証明済み |
| whereAccessible | OPEN。Covered/Accを一般に導出していない |
| treeExecution | OPEN |
| canonicalLocalOrder | OPEN |
| dictionaryRefl | 上流証明済み |
| evidenceNode | REFUTED。今回の無変更raw feedback境界。SourceFormed限定の別義務はOPEN |
| generatedChildren | OPEN。一般のstable selected適用性が残る |

## 検証・実行範囲

- Lean4.35.0の既存toolchain/cache再使用。初回focused651 jobs、次652、反例統合655、正例形成まで658 jobs、最終coherence/classifier込み661 jobs。
- 6小Audit shard、計113宣言（111公開定理と2証明certificate）の `lake env lean --trust=0` がPASS。
  propext/Classical.choice/Quot.sound以外の公理なし。sorry、新規axiom、native_decideなし。
- 独立読取りレビュー: raw反例の全5規則・非空モデル・否SourceFormed、正例の実feedback更新、
  モデル不要な可視性、Covered/Accの限定を確認してPASS。レビュー自身が独立再buildしたとは言わない。
- 全体のlake build、凍結した巨大Audit全体、全repository verificationは実行していない。
  上流の制限に従いfocused buildとdiff-only gateのみ。
- `boundary-input-inventory.py --check`は古い表の不足で最初FAIL。
  source/ledgerを確認して表へ21既存CommonRole項目を補い、再生成後PASS。
  CommonRole scope302/Main93/Audit302/ledger160。これはsemantic coverageや監査完了数ではない。
- 一時的な #check 補助ファイルをlean/直下に置いていたためdiff gateは一度FAIL。
  scratchへ移して再実行PASS。#checkの表示option誤記も修正して終了0で署名を取得。
  開発途中の試行を完成結果として数えていない。
- Y2: `notes/audit/x-oracle.md` の既存X1/X2/X8/X9を参照。今回のraw journalやexact refreshを
  Y2 sourceで直接表現できるoracleは用意していない。実機比較の新規実行なし。
  Leanの反例をY2の実行時バグやプログラム入力の反例と呼ばない。
  X1の宣言受理はjournal意味論を検査せず、X2の実行成功はadvertised whereの強制を示さない。
  X8/X9はdumpで要求する再帰μが成立せず、K2一致の根拠に採用されていない。
  これらの既存結果を今回の安定性・関連出力健全性の実機検証に流用していない。
- 利用量の枠は不明。

## 公開・復元

GitHub appで `work/dots-main` だけをexpected SHA付き・非forceで更新。
承認待ちなし。凍結Audit/READMEは変更せず、全中間ソースをbyte照合した。

1. `b903c7122d2d1e1c9dafa704b7f7861810cf0fca`: current journal、5ファイル。
2. `5cb603e793993c480c8347e50d10de5eae115021`: 有限treeとmodeled Joint阻害、10ファイル。
3. `a501b6647692b27626c64411c31ca83e0723f5f2`: 実EvidenceNode反証、13ファイル。
4. `feaa9f1c8fcdd89b97edef4c0cf97f4ef40a3dde`: SourceFormed正例と可視性等、22ファイル。
   tree `f84ad91cc3e100db77585c93136bf6c202c321e8` は非truncated2769 entries。
   全22変更ファイル＋凍結2ファイルのblob SHAが内容からの計算と全一致。
5. `592967999ce518979844bd35468bd2d88a4b703d`: view-changing exact refresh後のStable正例。
   第5バッチ7本文一致。累積26ファイルを公開。
6. 最終source `575433881b99d9d1e89a51de4cb53b234f846b87`: 最終classification、一般同一occurrence整合性。
   tree `ff7a4d3d1711a101f326578a181722e4f90efb9e` は非truncated2777 entries。
   全30変更ファイル＋凍結2ファイルの32 blob SHA一致。さらに最終source固定refから
   全30変更ファイルを個別に再取得し、全本文byte一致を再確認した。

心拍: 開始直後09:27、09:38（最初の10分目標から約1分遅れ）、09:47。
09:57、10:07にも独立心拍。最終終了時刻は末尾に記載。

## 次の候補（無断で境界を変えない）

1. 質問ノートに従い、EvidenceNodeをどの層でSourceFormed/到達可能状態に限定するか監督役が判断。
2. `sourceFormed_selected_simultaneous_branch`: alias全体について同一journalモデルでBranchAtを
   構成する。現在のsingletonキー整合性だけで十分と仮定しない。
3. `finished_refinement_source_transport`: view/carrier変更をsource識別子と検査結果の対応で扱う。
   今回の固定view混合trace theoremを無条件にview変更へ適用しない。

質問ノート: `notes/questions/2026-11-12-cycle138-stable-journal-evidence-scope.md`。
詳細module guideと全量化子付き署名は同日cycle138の設計ノートにある。

## Diff-only gate の出力全文

```text
verify-lean: . @ 0dc4a882d (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/Cycle136.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Finished.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Followup.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit_code: 0
```

## 定理名と日本語の主張

全ての量化子・暗黙roles・依存前提の**正確な型**は
[全署名](../design/2026-11-12-cycle138-theorem-signatures.md) に併記。
以下の「例」は各モジュール内の明示された固定registry/context/rootを指す。
公開宣言数は補助補題・具体例を含むもので、B4を113件解決した意味ではない。

### GeneralDictionaryCurrentJournal（任意roles/registry/context/root）
- `initial_current`: 空journalの全packet現在Instance条件は成立。
- `installed_current`: 実Installable packetを実installした後の任意Modelsから新packetの現在Instance。
- `step_current`: 任意の実restricted Stepと更新前Currentから更新後Current。
- `trace_current`: 任意有限restricted traceと更新前Currentから更新後Current。
- `initial_trace_current`: 任意の空journalからの実restricted traceの後はCurrent。
- `recorded_node`: 上のtrace・packet所属・最終Models・同モデルの全子Evidenceから親Evidence。

### GeneralDictionaryCurrentJournalExamples
- `actual_path`: 固定例のinstallとdescriptor変更refreshは実restricted trace。
- `recorded`: 親packetはrefresh後journalに記録されている。
- `current_parent`: 任意の最終Modelsについて親キー2/子1件の現在Instance。
- `no_original_extension`: 旧packetから最終contextへの普通のExtensionは偽。
- `nonvacuous_beyond_extension`: 実モデル・現在Instance・非Extensionが同時成立。
- `arbitrary_tail`: さらに任意の実restricted traceとその最終Modelsでも同親Instanceを保存。

### GeneralDictionaryJournalTree（任意state/root、uniform版は任意registry/contextも）
- `recorded_tree`: Coveredと全記録子辺Accから純粋Recorded判断の有限tree。
- `uniform_dictionary`: 実初期restricted trace・Covered・Accから、全最終Modelsに共通の同一treeとEvidence。
- `missing_packet`: 任意のReach可能siteで記録packetが皆無ならCoveredは偽。

### GeneralDictionaryModeledJointGap
- `stale_checked`: 固定不可視キー31の宣言自身はDeclarationChecked。
- `query`: 任意の同宣言idで検査queryが同じnominal形。
- `schema`: 任意id/その検査証明で生成要求は空。
- `every_branch`: 任意id/検査証明/元stateの任意Modelsで当該branchを満たす。
- `models_iff`: 任意modelで固定journal Modelsと元state Modelsが同値。
- `journal_model`: 固定journalの具体的モデルを構成。
- `known`: 元stateの全supported sourceがKnown。
- `generated_only_root`: 固定rootからGeneratedの任意childはroot自身。
- `no_install`: rootと同じoccurrenceを持つ任意packetは実Installableでない。
- `stable`: 固定journalは実feedback Stable。
- `not_joint`: 固定root/selectedキー30にJointは成立しない。
- `edge_shape`: 任意feedback Edgeの始点0・終点1。
- `acyclic`: 任意sourceにfeedback Cycleなし。
- `old_acyclic`: 任意旧slotに旧RecursAtなし。
- `report_calculated`: 固定宣言のreportを実際のcaptureとして計算。
- `linked`: 固定rootの需要はsource stateにLinked。
- `prepared`: 固定可視宣言はPrepared。
- `ready`: 固定rootはRootPendingでない。
- `survivor`: 可視キー30/子なしが元Survivor。
- `selected`: 同キー30/子なしが実feedback Local selected。
- `modeled_stable_selected_not_joint`: 具体モデル・Stable・selected・非Jointを同時に示す。
- `registry_checked`: 固定registryのChecked。
- `no_modeledSelectedJoint`: この具体的rolesの一般ModeledSelectedJoint義務を否定。
- `current_instance`: 任意journal Modelsで正しい現在Instanceキー30。
- `current_evidence`: 任意journal Modelsで正しい終端Evidenceキー30。
- `not_sourceFormed`: 固定journalはSourceFormedでない。

### GeneralDictionaryRefreshGap
- `no_known`: 任意stateが具体intモデルとstringモデルを両方持つならsource1はKnownでない。
- `good_journal_model`: raw反例journalにintモデルがある。
- `refresh_unknown`: 任意after contextと実exact Refresh証明でもsource1はKnownにならない。
- `generated_only_root`: 反例の任意Generated childはroot。
- `no_install`: rootと同じoccurrenceの任意packetは実Installableでない。
- `stable`: 反例が実feedbackの全5規則についてStable。
- `edge_shape`: 任意feedback Edgeは0→1。
- `acyclic`: 任意sourceにfeedback Cycleなし。
- `old_acyclic`: 任意旧slotに旧RecursAtなし。
- `selected`: 実feedback Local selected40[]。
- `no_evidenceNode`: 実Models/Stable/selectedと旧bad_not_evidenceから変更されていないV4義務を否定。
- `not_sourceFormed`: そのraw反例journalはSourceFormedでない。
- `no_bridges`: 任意executor/frontiersに対して、この具体的raw境界のB4Bridgesは成立しない。

### GeneralDictionarySourceChoiceVisibility（任意roles/registry/root/state）
- `visible`: SourceFormedなら任意の記録packet宣言がregistryに所属。Models前提なし。
- `singleton_choice`: さらに任意のsingleton宣言について、全記録宣言はその宣言に等しい。
- `singleton_key_coherence`: 上記前提で任意focusのalias packetキーがsingletonキーに一致。
- `singleton_selected_coherence`: さらに任意focus/key/childrenの実Local selectedからaliasキーが実selected keyに一致。

### GeneralDictionaryJournalTreeExamples
- `good_before`: 初期empty journalに具体モデル。
- `edge_shape`: 初期の任意feedback Edgeは0→1。
- `acyclic`: 初期の任意sourceにCycleなし。
- `old_acyclic`: 初期の任意旧slotにRecursAtなし。
- `selected`: 初期に実feedback selected40[]。
- `enabled`: 固定terminal packetは実feedback Installable。
- `feedback_step`: 固定before→afterは実feedback Step。
- `finished_step`: 同更新は普通のExtensionを伴う実restricted Step。
- `no_child`: afterの任意child/parentについて記録子辺はない。
- `covered`: afterのrootに純粋な記録網羅性。
- `accessible`: afterのrootに記録子辺Acc。
- `good_after`: afterに具体モデルが残る。
- `bad_excluded`: afterは旧string反例をモデルとして持たない。
- `uniform_dictionary`: afterの任意Modelsに共通の一つの有限treeと現在Evidence。

### GeneralDictionaryJournalTreeFormation
- `initial_source`: 正例の元context/rootは実InitialSource。
- `formed_before`: 正例の初期empty journalはSourceFormed。
- `formed_after`: 実feedback install後もSourceFormed。
- `reachable_positive`: 正例のSourceFormed・具体モデル・旧反例排除を同時に示す。

### GeneralDictionaryTerminalRefresh

固定の実SourceFormed正例を使用。モデル引数・変更先state/context/sourceの任意性は下記と全署名に明示。
- `refines`（証明定義）: source/support/private制約を保持する実Refinesを構成。
- `output_int`: 任意のinstallation後Modelsからsource1≃int。
- `certificate`（証明定義）: その方程式から実exact Refresh証明を構成。
- `source_known` / `source_unknown`: source1はrefresh後Known、直前はKnownでない。
- `actual_refresh`: 直前から直後への実feedback Step。
- `exact_models`: 任意modelで前後のjournal Modelsが同値。
- `formed`: 最終journalはSourceFormed。
- `inhabited`: 最終journalの具体的intモデル。
- `context_complete`: 任意raw source modelから最終journal Modelsを得る。
- `no_known_distinct`: 任意state/sourceと二つの指定された異なるscalarモデルから当該sourceがKnownでない。
- `varying_original`: 任意n≥2についてsource nだけ変えたモデルが元contextを満たす。
- `varying_model`: 同じ任意n≥2のモデルは最終journalも満たす。
- `refresh_large_unknown`: 任意の次context/実exact証明/n≥2でもnはKnownにできない。
- `current_query` / `current_schema`: 最終queryと生成schemaを直接計算。
- `every_current_branch`: 任意最終Modelsで実際の宣言branchが成立。
- `installs_committed`: rootと同じoccurrenceを持つ任意の実Installable packetは既にCommitted。
- `generated_only_root`: 最終rootから任意Generated childはroot。
- `stable`: 全5実更新規則について最終journalはStable。
- `current_instance` / `current_evidence`: 任意最終Modelsで新contextに現在Instance/終端Evidence。
- `completed`: SourceFormed・Stable・具体モデル・全最終Modelsで同じEvidenceを結合。

### GeneralDictionaryTerminalClassification

- `edge_shape`: 最終journalの任意feedback Edgeは0→1。予約IDの終点も可変モデルで除外。
- `acyclic`: 任意sourceに最終feedback Cycleなし。
- `old_acyclic`: 任意旧slotに最終旧RecursAtなし。
- `report_calculated`: 最終reportは指定capture。
- `prepared`: 所有済みallocationの再訪を許す実Freshにより最終宣言Prepared。
- `survivor`: 最終contextにSurvivor40[]。
- `selected`: 実feedback Localでselected40[]。
- `resolved`: SourceFormed・Stable・実selected・具体モデル・全最終ModelsでEvidenceを結合。
- `boundary_local`: 実feedback selectedを既存対応定理で無変更boundaryのLocalへ移す。
- `classified`: 無変更boundaryのClassifyは終端payload `.node 40 []` を選択。

- `GeneralDictionaryTerminalClassification.two_steps`: 正例の初期journalから最終journalまで、
  実feedback installationと実view-changing refreshの2更新を明示したSteps。

### GeneralDictionarySelectedInstanceCoherence（任意roles/registry/state/root/model）
- `instance_selected`: 同一context・同一occurrenceのInstanceと実selectedからキーと順序付き子列の一致。
- `recorded_selected`: 任意restricted初期trace、最終記録packet、任意最終Models、packet occurrenceの実選択から同一致。
- `recorded_at_selected`: さらに任意focusとpacket occurrenceが等しければ同じ結論。singleton制限なし。

修復を検討するためのregistry/provenance/rootの整合条件を
`notes/design/2026-11-12-cycle138-scope-repair-obligations.md` に分析した。
新target・新意味論の採用はしていない。

focused build、6監査の全出力、inventory、diff gateの全文は
[検証記録](../audit/2026-11-12-cycle138-focused-verification.md) に保存した。

## 終了

最終化開始: 2026-11-12T10:13:55Z（開始から46.6分）。ユーザーの55分上限を優先し、
必要な証明・検証・全ソース公開/照合・独立レビューが終わったため、追加の待機は行わない。
本報告、全検証記録、completed心拍を同じ最終commitで公開する。累積33ファイル
（ソース/設計等30 + 検証記録 + 本報告 + 心拍）。ソース30ファイルは最終sourceのまま。
最終commit/treeと公開後の照合完了は会話報告を参照。全proof worker終了、次サイクルまで新作業なし。
