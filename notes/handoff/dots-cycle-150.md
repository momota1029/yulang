# dots cycle150 — recursive nominal trees and same-model alias Evidence

開始2026-11-12T21:27:19UTC。報告22:17UTC、55分期限22:22:19UTC。一般V5は **6/14供給・8/14未解決**。

## 復旧・公開
fresh integration/m1-final6cff680ccafc24ab298e1b890adcb6d7bba15034、standing orders/I25を再読。前149のwriter不存在を確認。未応答tree操作は盲目的に再試行せず、local tree404とremote head不変を確認して異なる小分けtree操作で回復。前149最終32modules186定理を639ab803742ac6ffb4ace3e67acc613bcb108684へ公開、tree一致。前149の期限超過はcrash記録と回復報告に明記した。

今回の主sourceは20ab8fa1f53e335f43fb33f21153f18cc788c87d、tree5f3474830857573c562ed183e2a9e0b3836aa379をremote取得してlocal一致。Core CI43316112882、Lean kernel43316112773は22:17再取得でsuccess。後述の最終8定理・報告追加commitのCI成功を意味しない。

## 証明した範囲
17新規modules、99公開定理。回復149の186定理とは別に数える。
- 任意有限の実named/no-merge更新からsites namingと空aliasを帰納し、最終localityを仮定せずJointを導く。新規occurrenceの構造的命名条件は残る。
- 異なるoccurrence/child ID・出力要求を持つalias siteを、同じ一つのcurrent modelで扱う。記録packetのreplayまたは実chosen declarationのTree/scalar構造からbranchを導く。ordinary trace、既存Scheduled証明、各Related siteのselected/coverageは残る。
- 任意有限の再帰的binary nominal treeについて、実inspection・capture・正確なbinding allocation・private Modelsを構成し、terminal無出力のBranchModels/Instance/Evidenceへ接続。内部辺point、全binder名injective。葉binder区間は任意。任意arity・繰返しbinder・nonpoint内部辺は未証明。
- 実3slot/5slotモデルで、旧unary spine/旧single-forkでは表せない形を証明。最終追加8定理で5slot例を実InitialSource、空journal Models、V5 Reachable(refl)、同一model Instance/Evidenceへ接続。Stableやcurrent-selectedは主張しない。
- 既存の一般ClassifyとEvidenceのまま、任意有限辞書の相互帰納へTree leafを接続。実ordinary traceからpacket Extensionを導く。明示structural coverageと有限Classify証拠は依然必要であり、一般coverage/実行停止/完全性/主型性の完成ではない。

完全な型はdots-cycle-150-types-1〜3.md（最初の91定理）、最終追加8定理はdots-cycle-150-initial-validation.md。module guideと各設計ノートが仮定・接続を示す。

## 一般残差
selected後のsupport guard不足ではなく、初回未記録nonterminalのJointが焦点。EdgeOriginのpacket回収自体がJointを仮定するので、coverageを先に得てJointを導く案は循環。unrestricted mergeのcross-key整合も一般には未導出。モデルを失うだけのmergeはEvidence反例にならない。実reachable+stable+inhabited反例は確立していない。詳細dots-cycle150-general-evidence-residual.md。

## 13boundary fields
|項目|状態|
|---|---|
|Checked|一般定義あり|
|Models|一般journal定義あり|
|RootPending|一般定義あり|
|RootK2|一般定義あり|
|CandidateK2|一般定義あり|
|InspectionPending|一般定義あり|
|Survivor|一般recursive定義あり|
|Reorders|一般定義あり|
|DictionaryEquivalent|一般定義あり|
|Step|一般support更新定義あり|
|Stable|一般定義あり|
|Generated|一般履歴graph定義あり|
|Evidence|一般model-indexed定義あり、一般橋未完|
定義の存在と橋完成は別。Initialは空journal InitialSource、実reachable範囲を維持。

## 検証と制限
- 回復149:focused32modules730jobs、audit186、全431宣言gate、diff gateすべてexit0。
- 今回最初16modules91定理:focused748jobs --wfail、trust0 audit、全361宣言gate、全型出力、diff gate exit0。完全出力はdots-cycle-150-validation.md。
- 最終Initial例8定理:focused build、99定理trust0 audit、99型出力exit0。17modules全宣言gateは中断により結果未確認。旧361宣言gateを新17modules全体の成功と混同しない。
- frozen Audit.lean/README、既存意味論/target未変更。全体local build・Yulang2実機未実行。spec6.2/6.3と公開済Yulang2 X1 oracleを照合したが、旧runtime受理は一般Lean証明や新実装検証ではない。
- 開発中のgate引数不足、未commitによるdiff gate、type-print表示option誤りは修正後pass。証明を弱めて通していない。
- 22:04頃から処理継続が中断し22:16:42に復帰。22:06予定heartbeatを欠落した。再開後新規証明を止め、検証済差分・途中成果・報告の公開とwriter解放を優先した。継続監視が正常だったとは主張しない。
- 追加承認要求なし。一般V5の8残件は減っていない。次回は最終headと本報告を取り直し、初回Jointの独立構成または厳密な実反例条件を優先する。

## 最終差分gate（exit0）
`tools/verify-lean.sh . origin/integration/m1-final --no-build`
```text
verify-lean: . @ 4da7eb5c3 (base origin/integration/m1-final)
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
