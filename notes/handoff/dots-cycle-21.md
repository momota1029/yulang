# Yulang Lean cycle 21

開始 2026-11-09T00:29:56Z、基点 integration/m1-final `490a9a7a2`。
最新standing/inbox I-4〜I-10を再読、ACTIVE、最大24。前回20はcompletedで報告あり、並行writerなし。
上流をmergeして既存作業場を再使用。ユーザーの25分上限とfocused-onlyを優先。

## 成果・境界

新しい2モジュールで、独立に定義された合法Traceのどの閉じた実行順も同じ更新ID集合を持ち、
実関連型のordinaryモデル集合が一致する、という橋を証明した。
**EmissionMonotoneが明示的前提**。追加更新で以前のemitが失われない（同じsource nodeは不要）条件。
実source-associated adapterがこの条件を満たすことは未証明で、一般にはReachが消える可能性がある。
したがって実adapterの無条件順序独立やB4完成を主張しない。条件を隠さずdocstringにも記した。
単なる固定例ではなく全有限update数・registry・root・adapterを量化する条件付き一般補題。

## 定理の日本語主張（量化子と前提）

FeedbackConfluenceの定理は任意n,k, registry, SourceRequest nのroot、
decode : List (Fin k) → State n、emit : Node registry root → List (Fin k)を量化。
Closed s は「Reach(decode s)の全nodeがemitする全IDがsに属す」という独立判断。
EmissionMonotoneは任意a⊆bとID fで、aでReachなあるnodeがfをemitするならbでもあるReach nodeがfをemitすること。

- `CommonRoleFeedbackConfluence.trace_subset_closed`（健全性の補助）:
  EmissionMonotone、任意start/finish/bound、Trace start finish、start⊆bound、Closed boundの下でfinish⊆bound。
- `closed_traces_same_facts`（健全性/完全性の補助）:
  EmissionMonotone、任意a,b、Trace [] a、Trace [] b、Closed a、Closed bの下で任意fについてf∈a ↔ f∈b。
- `collect_is_closed`（補助）: すべての上記入力で実collectはClosed。単調性の前提は不要。
- `collect_least`（健全性の補助）: EmissionMonotone、任意boundとClosed boundの下でcollect⊆bound。
- `collect_exact_closed_trace`（健全性/完全性の補助）:
  EmissionMonotone、任意finish、Trace [] finish、Closed finishの下で全fについてf∈collect ↔ f∈finish。

AssociatedConfluenceは更に任意env : AssocEnv、roles、wf : WellFormed env.cores、seed : State n、
有限table : Fin k → Request nを量化。decodeは実AssociatedBatch.run、receiverはRequestに固定される。
- `CommonRoleAssociatedConfluence.same_facts_same_models`（健全性/完全性の補助）:
  任意a,b、全iでi∈a ↔ i∈bの前提の下で、任意assignmentに対してdecode aの全atomsを満たす iff decode bの全atomsを満たす。
  順序や重複は任意。Reach単調性の前提は不要。
- `closed_histories_same_models`（健全性/完全性の補助）:
  任意registry/root/emit、実decodeに対するEmissionMonotone、任意a,b、両者への空からのTrace、
  Closed aとClosed bの下で、全assignmentに対して実decode aとbのモデル条件が同値。
- `final_models_exact_closed_history`（健全性/完全性の補助）:
  同じ実decode/emitのEmissionMonotone、任意finish、Trace [] finish、Closed finishの下で、
  全assignmentについて実finalStateのモデル条件 iff 実decode finishのモデル条件。

新しい主型性定理なし。制限は仕様の拒否規則ではなく、実装の断片と追加証明義務。
B4の一般形は**5橋とも残る**。bridge2内の順序独立を閉じるための十分条件を特定した段階。
実source lowering、変動receiver、独立診断tree、一般resolve_exact、X13〜16の外側PROVEDは未達。
次の候補: (1) 実adapterでEmissionMonotoneが成り立つ範囲を証明または反例を出しdriverを修正、
(2) 実source注釈の導出、(3) 子結果を保持した独立診断tree。
質問ノート追加なし（意味論を選択していない）。

## 検証

`git fetch origin integration/m1-final:refs/remotes/origin/integration/m1-final` 成功。
`git fetch origin work/dots-main:refs/remotes/origin/work/dots-main` 成功。
`git merge origin/integration/m1-final --no-edit` 成功。
`git fetch origin work/dots-audit:refs/remotes/origin/work/dots-audit` 成功。
既存elan/Lean4 v4.35.0とcacheを再使用。
`timeout 180 lake build --wfail Yulang.CommonRoleFeedbackConfluence`: exit0、289 jobs、1.5s。
`timeout 180 lake build --wfail Yulang.CommonRoleAssociatedConfluence`: exit0、292 jobs、1.0s。全文:
```text
✔ [292/292] Built Yulang.CommonRoleAssociatedConfluence (1.0s)
Build completed successfully (292 jobs).
```
`lake env lean /tmp/cycle21-audit.lean`: exit0。全文:
```text
'Yulang.CommonRoleFeedbackConfluence.trace_subset_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackConfluence.closed_traces_same_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleFeedbackConfluence.collect_is_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackConfluence.collect_least' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackConfluence.collect_exact_closed_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAssociatedConfluence.same_facts_same_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedConfluence.closed_histories_same_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAssociatedConfluence.final_models_exact_closed_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
8定理はpropext/Classical.choice/Quot.soundのみ。sorry/new axiom/native_decideなし。
`git diff --check`成功。全体build/全Audit/verify-lean.shは最新指示どおり未実行。
verify-lean.shの出力/終了コードは存在しない。全体PASSとは報告しない。
初回focusedから成功、中断なし。

## Yulang2との照合

最新監査枝のx-oracle X13–16を読んだ。旧実機のcheck成功は内部traceの単調性を証明しない。
今回の内部判断は実機から直接観察できず未照合。spec6.3の連言の順序独立を追加仮定の証明と混同しない。

## 公開・資源

ローカルcommit f0b1f5589、5eab98d78、fb16c581e。
開始心拍c57973ae。自作成果6pathsをcontents APIで1ファイルずつ公開。
Yulang/Audit/READMEはremote基点blob一致を確認しメモリ内で末尾追記。
公開ac15ab38bをfetchし、全Lean treeと新設計ノートのローカルとの差分なしを確認。
integration/m1-finalが公開branchの祖先であることをexit0で確認。
この報告とcompleted心拍を含め自作公開8paths。work/dots-main以外への書き込みなし。
空き容量開始19GB、終了19GB。cacheコピーなし、環境再作成なし、公開承認待ちなし。
使用量枠への計上は不明。最終所要時間/公開hashは完了報告で確認。現時点約6分。
