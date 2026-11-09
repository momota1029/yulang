# Yulang Lean cycle25

開始 2026-11-09T03:57:20Z。integration/m1-final `7cffd2f27` を取得して
standing orders/inbox I-11 を再読。ACTIVE、最大サイクル数は廃止されていた。
前回cycle24 completedと報告を確認。今回が上限廃止後の再開であり、復旧ではない。
同一作業場とキャッシュを使用、前回writerなし。統合版をmergeした。

## 部分目標

祖先候補の履歴を保持する状態非依存の有限carrierと、history-specificな
関連型方程式viewのexactness。**この限定した部分目標は閉じた。**
全祖先(parent source node,candidate)を履歴に保存することで、同じsourceへ
合流した別の候補経路が、別経路のguardを借りて活性化されることを防ぐ。
一般B4の完了ではない。3新モジュール、14定理。新規主型性定理はない。

## 定理（量化と前提、省略しない）

P=CommonRoleCorrelatedPaths、C=CommonRoleCorrelatedCarrier、
E=CommonRoleCorrelatedEquations。
共通量化: 全自然数n、Paterson検査済Registry R、source root、
全履歴依存Boolean mask、固定観測ordinary state s。
sourceは既存のint-only・unary・capture-bearing断片。
Routeは祖先(parent node,candidate)の逆順列と現在node。

- P.children_exact: 全route r,tについて実children所属 iff 登録候補dとchild cが存在し、その履歴のmask・独立Inspect・source置換でtがrを一歩拡張したもの。（健全性/完全性補助）
- P.pathsUpTo_exact: 全fuelとroute rについて有限列挙所属 iff 独立Path rかつ履歴長≤fuel。（健全性/完全性補助）
- P.path_measure: 全独立Path rについて履歴長＋現在sourceWeight≤root sourceWeight。checked Patersonの減少から導出。（停止補助）
- P.collect_exact: 全route rについて内部で導いたroot sourceWeightを上限とする列挙所属 iff 独立Path r。外部fuel/閉包証明なし。（健全性/完全性補助）
- P.extend_history_injective: 全route r,t、候補d,e、子c,uについて拡張routeが等しければr=t,d=e,c=u。（相関保持補助）
- C.active_child_retained: 全active一歩辺がstate/mask非依存の構造的childrenに属する。（保持補助）
- C.pathsUpTo_retained: 全fuelとrouteについてactive列挙所属なら静的列挙所属。（保持補助）
- C.path_retained: 全state/maskで独立Pathを持つrouteは同じ固定有限carrierに属する。（保持補助）
- E.entries_exact: 全annotation写像A、route r、候補d、固定receiver要求qについて保存entry所属 iff rが静的carrierに属し、dが登録済みで、q∈A(r,d)。（健全性/完全性補助）
- E.activate_exact: 全A,r,d,qについて活性entry所属 iff 同じrの独立Path・d登録・同じ履歴のmask・独立Candidate・q∈A(r,d)。（健全性/完全性補助）
- E.entry_retained: 全state/mask,A,r,d,qについてPath r、登録d、q∈A(r,d)ならentryはstate/mask非依存の保存carrierに属する。（保持補助）
- E.disabled_history_excluded: 全A,r,d,qについてmask r d=falseなら同じtipへの別routeの支持によって(r,d,q)が活性化されることはない。（健全性補助）
- E.view_exact: 全associated env/roles、core WellFormed、A、seed、assignmentで、実viewのモデル iff seedモデルかつ全Path r・登録d・有効mask・独立Candidate・A(r,d)内の全qについて、実Computedの全出力等式を満たす。（健全性/完全性補助）
- E.view_declarative_exact: 前項にAssocWellFormedを明示的に仮定し、Computedを独立associated宣言導出に置き換えたiff。（健全性/完全性補助）

## 限界・残りの5橋

B4の主定理には依然5橋（source boundary、全generated workの閉包、飽和停止と意味閉包、
独立最終分類、辞書健全性と順序同値）が残る。今回はbridge2内部の候補祖先相関の部分目標。
mask/観測/固定receiver annotationは入力。保持は全状態でactiveになるrouteを含むという
主張であり、更新後もactiveのままという主張ではない。各経路は一つの観測状態で評価。
duplicate where occurrence indexは区別せず、兄弟の大域的候補選択整合性は未証明。
深さ上限は実用的計算量を保証しない。source lowering、正しい候補選択、feedback固定点、
一般B4、X13〜X16の外側入口PROVEDは未達。意味論の選択は行っていない。
次の候補: (1)共同の兄弟選択と祖先条件を満たすbranch環境、(2)guard再検証を伴う安定化、
(3)source loweringからannotation/choiceを生成する橋。
新質問ノートは無し。cycle24の候補guard方針質問を引き継ぎ、設計ノートに境界を明記。

## 検証と制限

`cd lean && lake build --wfail Yulang.CommonRoleCorrelatedEquations`: exit0、297 jobs。
`lake env lean --trust=0 /tmp/cycle25-audit.lean`: exit0、14定理、標準3公理のみ。
`git diff --check`: PASS。新sorry/axiom/native_decideなし。
独立読取りレビューで不整合なし。全体lake build、全Audit、verify-lean.shは
指示に従い未実行。従って全体検証の出力・終了コード・PASS主張なし。

Yulang2との照合: 最新work/dots-auditの読み取りfetchを試したが、auto-reviewが
「停止済み監査タスクの範囲外」と拒否した。監査作業再開/書込みはしていない。
拒否を回避する試行はせず、今回の最新実機照合は未実施とする。
既存cycle24報告のX13〜16境界とspec6.3の兄弟安定まで遅延を参照した。
今回のcarrierは言語受理規則の変更ではない。

開始空き19GB、作業場・キャッシュの複製なし。使用量枠は不明。
部分目標が閉じたため時間埋めの補題を増やさず公開へ移る。

### focused build 全文
```text
✔ [295/297] Built Yulang.CommonRoleCorrelatedPaths (1.1s)
✔ [296/297] Built Yulang.CommonRoleCorrelatedCarrier (1.0s)
✔ [297/297] Built Yulang.CommonRoleCorrelatedEquations (1.0s)
Build completed successfully (297 jobs).
```
### trust=0 公理監査 全文
```text
'Yulang.CommonRoleCorrelatedPaths.children_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedPaths.pathsUpTo_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedPaths.path_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedPaths.collect_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedPaths.extend_history_injective' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCorrelatedCarrier.active_child_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedCarrier.pathsUpTo_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedCarrier.path_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedEquations.entries_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCorrelatedEquations.activate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedEquations.entry_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedEquations.disabled_history_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCorrelatedEquations.view_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCorrelatedEquations.view_declarative_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 公開

10ファイル（新Lean3、追記3、design1、design index1、report1、heartbeat1）。
GitHubアプリ経由の個別blob→小さいSHA tree→非force/expected-head一括更新。
公開後にremote treeとlocal treeの一致を確認する。確定commit・最終所要時間は親報告。
