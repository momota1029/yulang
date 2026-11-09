# Yulang Lean cycle23

通知 2026-11-09T01:27:19Z。前cycle22の復旧公開を待ち、実作業開始01:31:11Z。
最新integration/m1-final `3181de1ac` を取得、standing orders/inbox I-11、ACTIVE、最大24を確認。
前回は復旧済みcompleted・報告あり。今回並行writerなし。同一作業場を再利用。

## 部分目標

最終source支持を失う非単調feedbackに対し、全有限token集合を再検証して
自己支持する候補を漏れなく列挙し、最終方程式のモデルexactnessを得る。
**診断用の有限断片として閉じた**。言語resolverの修復・B4の完成ではない。

Cycle22の反例を、任意ordinary更新から実チェック済み関連型宣言の計算へ強めた。
`Index(box int, int).value = int` が共有slotを絞るとfirst-hit childが消える。
空集合ではchildがtokenを要求し、tokenを入れるとchildが消え、両方の候補が不適格。
associated-only decodingでも一般EmissionMonotoneは偽。table/child associationは
有限入力として与えており、source parserからそのannotationが生成される証明はない。
frontierはpending→ambiguousであり、言語上のselectedではない。

searchはこの不具合を検出する補助であり、空の結果を言語エラーと解釈しない。
複数候補・矛盾候補・自己正当化的支持を排除せず、最小解や辞書を選ばない。

## 定理（全量化と前提、側）

SupportSearchでは全n,k、checked registry、source root、decode:List(Fin k)→State n、
emit:Node→List(Fin k)を量化。associated版は全env,roles,wf:WellFormed、seed、
固定receiverのtable、assignmentを量化。全て補助結果で、主型性の新定理なし。

- filter_mem_subsets: 全型α、Bool述語p、有限リストxsについてfilter p xsがsubsets xsに含まれる（網羅性補助）。
- subsets_length: 全α,xsについて列挙長は2^length xs（停止・大きさ補助）。
- subset_of_mem_subsets: 全α,xs,ysでys∈subsets xsならys⊆xs（健全性補助）。
- check_exact: 全seenで実行可能check=true iff 全token iについてi∈seen iff decode seenでReachなqがiをemit（健全性/完全性補助）。
- search_exact: 全seenで出力所属 iff 正準列挙への所属かつ上記独立支持判断（健全性/完全性補助）。
- canonical_complete: 全seen、そのfinRange順の正準表現がSupportedならその表現をsearchが返す（完全性補助）。元の任意順序がSupportedなら十分とは主張しない。
- search_capacity: 全入力で出力長≤2^k（停止・サイズ補助、効率性の主張ではない）。
- empty_exact: search=[] iff 正準なSupported候補が存在しない（診断完全性補助、言語の拒否規則ではない）。
- models_exact: 全found候補seenと全assignmentで、decode seenのモデル iff seedモデルかつ全最終Reach q・全i∈emit q・全Computed headについて出力slotがheadとEquivalent（健全性/完全性補助）。
- source_models_exact: 任意source annotationに実computed table/emitを用い、全found seen、assignmentで同じiff。右辺は全Reach q、全r∈annotation q、全Computed headの等式（健全性/完全性補助）。
- source_declarative_models_exact: さらにAssocWellFormed env rolesを明示前提とし、Computedを独立DeclarativeComputed（既知receiver・独立Resolves・AssocDerives）に置換した同じiff（健全性/完全性補助）。

SupportSearchBoundaryの6定理は上の一般searchの境界例。
- actual_associated_value: 実checked boxImplからrequestのintを計算（補助）。
- decode_empty / decode_singleton: 有限token空集合はbefore、[0]はafter（補助）。
- no_emission_after: 全Node qでafterにReachならemit q=[]（反例補助）。
- no_supported_candidate: この実関連型decoderでsearch=[]（存在保証への反例）。
- associated_not_monotone: この実関連型decoder/child associationでEmissionMonotoneは偽（一般単調性への反例）。

## B4の残り

一般B4の5橋は依然残る。本cycleはbridge2内部の支持再検証を閉じたが、
非単調first-hitの言語としての正しい飽和は閉じていない。
次の候補: (1)候補guardを保持した関連型方程式carrier、(2)独立診断treeと安定化、
(3)source loweringからannotation/tableを導出する橋。
動的receiver、全B4 resolve_exact、X13〜X16外側入口PROVEDは未達。
質問ノート1本。意味論は変更せず、spec6.3の遅延規則を維持。

## 検証

focused `lake build --wfail Yulang.CommonRoleSupportSearchBoundary` exit0、297 jobs。
`lake env lean --trust=0 /tmp/cycle23-audit.lean` exit0、17定理、標準3公理のみ。
新sorry/axiom/native_decideなし。git diff --check成功。
全体lake build、全Audit、verify-lean.shは指示により未実行（出力・終了コードなし）。
実機Yulang2は新規実行なし。最新監査x-oracleのX13〜16を参照したが、
今回の内部token支持は観測対象外。旧世代の成功をこの定理の検証に使わない。
読取りレビューで主定理の問題なし、最小/grounded解は主張しないと確認。

初回lakeをrepo rootから--dirで起動したときtoolchain未設定エラー、cd leanに修正。
具体反例のdecideは既存saturateのproof reductionで止まり、独立Reach証明に置換。
中断/環境再生成なし。作業開始空き19GB、キャッシュ複製なし。

Focused log全文:
```text
✔ [296/297] Built Yulang.CommonRoleSupportSearch (1.2s)
✔ [297/297] Built Yulang.CommonRoleSupportSearchBoundary (1.0s)
Build completed successfully (297 jobs).
```
公理監査全文:
```text
'Yulang.CommonRoleSupportSearch.filter_mem_subsets' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSupportSearch.subsets_length' depends on axioms: [propext]
'Yulang.CommonRoleSupportSearch.subset_of_mem_subsets' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSupportSearch.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearch.search_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearch.canonical_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearch.search_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearch.empty_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearch.models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearch.source_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearch.source_declarative_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSupportSearchBoundary.actual_associated_value' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSupportSearchBoundary.decode_empty' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSupportSearchBoundary.decode_singleton' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSupportSearchBoundary.no_emission_after' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSupportSearchBoundary.no_supported_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSupportSearchBoundary.associated_not_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 公開

work/dots-mainのみへ個別blob作成後、小さなSHA treeと非force expected-head一括更新。
前回大きなinline treeが停止したため、内容とtree送信を分離。公開単位は1 commit。
9ファイル（新Lean2、追記3、design1、question1、report1、heartbeat1）。
公開後、fetchしたremote treeとlocal treeの一致を確認する。
公開commitと最終所要時間は親への完了報告に記す。使用量計上枠は不明。
実装が閉じたので時間を埋める補題は追加せず、公開照合へ移る。
