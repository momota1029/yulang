# dots cycle151 — stable real aliases and nonterminal dictionary evidence

開始2026-11-12T22:25:17Z。自動実行runは22:27:19Z、55分上限23:22:19Z（自己期限23:20Z）。最終時刻はcompleted心拍。親から終了・writer解放指示を受け、追加作業を止めて報告する。一般V5は **6/14供給・8/14未解決**。

## 復元・公開
fresh integration/m1-final `09a135f9e63bdefa90f1918a5b2281594f087eea`、standing orders、inbox I25 ACTIVEを再読、STOPなし。前150writer解放済。integrationを取り込みINDEXの追加同士だけを併合。前150の最後の17modules・375全宣言監査をtrust=0で補完PASS。今回178定理と前回99定理を混同しない。

全source公開 `a3847a44866aa8d29c60ed86bf7d756236bafa0d`、tree `d64a2dc59c0b9f348ccb6bffecdaba71d2a7cba6`。remote取得とlocal全tree完全一致を確認済み。Core CI43325090468、Lean inference kernel43325090684ともsuccess（このsource SHAに対する結果）。以後の文書・心拍commitのCI成功を意味しない。中間成果636e4f5d、復旧7579f5b6も公開済み。

## 証明した範囲と前提
28新規Lean modules、178公開定理、486全宣言。全定理名は[dots-cycle-151-theorems.md](dots-cycle-151-theorems.md)、量化子・全前提・結論はdots-cycle-151-types-1.md〜11.md。全module名は[guide](../design/dots-cycle151-module-guide.md)。以下の構造条件を一般条件と取り違えない。

1. **非terminal variable where**。任意checked declarationのwhere入力がvariableへ正規化され各child出力要求が空なら、実materialization requestsが空になる。実childrenは消さない。任意有限binary nominal tree、point内部辺、injective binder名、lookup・RootDefined等の明示条件から独立private Models、同一model BranchModels/Instanceを構成。`emitted_children_length`系列は実children数とrequirements数を接続する。一般arity・重複binder・nonpoint辺は対象外。
2. **同一modelでalias全体を構成**。`UnrecordedAliasLeafJoint` / `UnrecordedVariableJoint`は全Related siteで同一chosen declarationの構造条件と実選択を要求する。ordinary InitialSource traceから旧packet整合を導き、同じ一つのcurrent modelに全BranchAtを構成してJointを導く。ordinary traceはguarded mergeを含むがrefresh/reobserveは含まない。Jointや結論のBranchModelsをそのまま仮定していない。
3. **有限辞書のrecursive soundness**。`VariableStableCoverage.dictionary_evidence`は任意InitialSource、ordinary trace、Stable、Generatedな各selected focusの実packet所属または上記structural coverage、任意current model、実有限ClassifyからEvidenceを導く。Jointを先に導いてからStableを使い実childrenのGeneratedを得る。無制限のreachable stateにcoverageが成立すること、実行停止、完全性・主型性は証明していない。
4. **実nonterminal初回install例**。List headにwhere childを一つ持つchecked registryで、実InitialSource、Reachable、inhabited、root/childの実選択、2node Classify、同一model Evidenceを証明。guarded first installが実際に可能なので初期状態は **not Stable**。選択済みであることを最終安定と偽っていない。
5. **実2identity aliasの安定正例**。既存失敗例は変えずscalar宣言を追加した新registry。InitialSource→親install→異なるchild10/11の実guarded merge。両者unrecordedかつ同一alias、共通modelでJoint。`stable_classified_dictionary`は同時にReachable、Models、全更新に対するStable、3node Classify、全current model Evidenceを証明。refresh/equate/reobserve/enqueue/merge/installすべてを検査。parentはnonterminalだがchildrenはterminal scalar・無named-output。一般alias整合を証明したのではない。実例を一般VariableStableCoverageにも接続した。
6. **観測済みscalar named output**。`ObservedScalarRequests.generated_models`は任意有限実requestlistの各targetが既存source slotで対応scalar観測と翻訳を持つ条件から全materialization Modelsを導く。variables=[]とunknown=falseも証明し省略しない。`ObservedTreeBranch`はroot named要求を保持し、実childを持つtreeに接続する。実List/where-child/out=int例でrequestはsingleton、空ではない。この追加例についてInitialSource・Stable・full child Evidenceまでは主張しない。
7. **条件付き単一node拡張**。`ObservedAliasJoint.ordinary_stable_evidence`は上記named-output Shapeまたは従来Shapeを全Related siteに要求し、InitialSource＋ordinary trace＋Stable＋実選択＋current Models＋実children Evidenceから親Evidenceを導く。recursive coverage定理にnamed拡張を組み込んだとは言わない。独立レビューPASS。
8. **阻害条件の切出し**。`SelectedAliasConflict.support_different_selected_no_joint`等4定理は同一alias classの実selected keysが異なればJoint不能と示す含意。異なるkeysのReachable＋Stable状態そのものを構成したわけではなく、一般V5反例ではない。disjoint-output案の未解決義務を設計ノートへ明記。

## 受入条件・13boundary fields
Checked、Models、RootPending、RootK2、CandidateK2、InspectionPending、Survivor、Reorders、DictionaryEquivalent、Step、Stable、Generated、Evidenceの13定義は存在する。定義の存在と橋の完成を区別する。

V5の未解決8: progress、execution、halted、whereAccessible、treeExecution、canonicalLocalOrder、evidenceNode、generatedChildren。今回はI25の到達可能な実状態の正例と条件付きsoundnessを強化したが、一般フィールドを新たに閉じていない。特にProgress、JointAtSelected、whereAccessible、canonicalLocalOrderの一般残差は残る。

I24凍結Audit.lean/READMEは変更なし。新監査はAudit/Cycle151.lean。spec/notes/plan/lake設定・監督役定義は変更なし。spec6.2/6.3との比較ではvisible registry、where子保持、associated equation、実K2を維持。Yulang2実機は実行環境に見当たらず未実行。監督役termination planの無限schedule案をLean counterexecutionとして数えない。

## 検証
- focused `lake build <28 modules> --wfail`: exit0、771jobs PASS。
- `lake env lean --trust=0 Audit/Cycle151.lean`: exit0、178定理PASS。公開tree照合後に同監査を再実行しexit0。
- focused全宣言gate: exit0、486 declarations PASS。許可依存はpropext/Classical.choice/Quot.soundのみ。
- 完全型出力: exit0。量化子・前提を含む11分割文書を公開。
- 前150全宣言gate: exit0、375 declarations PASS。
- 差分verifyのみ: exit0、以下全文。全体lake build/全module auditは常設制限に従い行わず、監督役へ委ねる。
- source CI: [Core](https://github.com/momota1029/yulang/actions/runs/43325090468)、[Lean](https://github.com/momota1029/yulang/actions/runs/43325090684) success。

全コマンド・focused出力全文は[dots-cycle-151-validation.md](dots-cycle-151-validation.md)、復旧ログはrecovery-validation。公開完了の報告時刻/最終SHAはcompleted心拍とこの報告を含むcommitで確認する。

```text
verify-lean: yulang @ 5b8e04c30 (base origin/integration/m1-final)
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
ok: lean/Audit/Cycle143.lean only appended (plus top import lines)
ok: lean/Audit/Cycle144.lean only appended (plus top import lines)
ok: lean/Audit/Cycle145.lean only appended (plus top import lines)
ok: lean/Audit/Cycle146.lean only appended (plus top import lines)
ok: lean/Audit/Cycle147.lean only appended (plus top import lines)
ok: lean/Audit/Cycle148.lean only appended (plus top import lines)
ok: lean/Audit/Cycle149.lean only appended (plus top import lines)
ok: lean/Audit/Cycle150.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupport.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupportOrder.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit code: 0
```

## 残る仕事（次の1〜3候補）
1. 実aliasのselected-key agreementを導く、またはdisjoint-output候補についてReachable・Stable・inhabited・子Evidence・bad modelを全て形式化して初めて反例性を判定する。
2. ObservedScalarRequestsをfresh target/non-scalar materializationへ拡張する。観測済みという仮定を隠さない。
3. ordinary trace以外のrefresh/reobserve transportと無制限reachable stateのstructural coverageを証明する。停止やJointを仮定に戻さない。

## 制限・中断・質問・公開量
新しい意味論の判断はしていない。新質問はなく、未証明候補の証明義務をdesign noteに残した。既存失敗例や定理は弱めない。全追加証明sorry/new axiom/native_decideなし。
初期background recoveryの結果未取得をPASS扱いせず再実行し、最初のPATH不足exit127を明示toolchainで修正、最後に375宣言PASS。初期心拍のupdatedを誤って未来22:29にした点は補正・復旧ログ記録済み。今回証明開発上の通常Leanエラーは最終build/gateで解消。公開は小さなinline tree batchで行い、今回承認待ち・失敗はない。使用量枠不明。検証終了後、親から期限優先終了指示を受けてwriter解放する。

integrationとの差分は最終報告・scope review・theorem indexを含め68files（Lean28modules＋imports＋audit、設計/検証/心拍文書）。cache/は既存未追跡物で公開しない。
