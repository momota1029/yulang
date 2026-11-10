# 保持した区間treeの全再帰診断を読む

状態: Draft、既存の固定Form断片についての証明設計。新しい言語意味論を決めない。

## 部分目標
cycle92の未完成childを含むtreeから実際に取り出す全到達nodeとunsupported診断を、cycle90の独立Reachへ接続する。最初のmissing childやzero-plan branchの後の診断も落ちないことを、任意registry/goalについて閉じる。

## データと独立判断
Treeは既存のdeclaration/bindings/local demands/全childを持つものをそのまま使う。`nodes : Tree α → List (Tree α)` はpreorderの全node、`goals := nodes.map root`。`boundaries`と`failures`はnodes上の各outside/rejectsをflattenする。子のplanやordinaryの充足可能性は参照しない。
独立判断は既存`CommonRoleIntervalWorkClosure.Reach registry root goal`と`Accepts`/`Rejects`で、tree所属から定義しない。宣言checkerの計算拒否は既存Paterson断片の制限であり、最終言語分類ではない。

## 型と最短の鎖
任意Checked registry、slots、Sources、rootで:
1. accepted candidatesから生成する全child列が既存children列と等しい。
2. `nodes (build ...) = (closure registry checked root).map (build registry checked slots sources)`。順序・重複を含む完全なリスト等式。
3. 実treeのboundariesが既存boundariesと等しい。任意goal/dで、その所属は`Reach registry root goal ∧ d ∈ registry ∧ inspect d goal = none`とiff。
4. failure所属は同じReachかつregistry所属かつ独立Rejectsとiff。
5. runはcheckerを計算するので、任意registryで存在するreturned tree上の診断所属は`Checked registry ∧ ...`とiff。callerのfuel、有限visit列、child-success、モデル存在は要求しない。
これらは診断列の健全性/完全性の補助で、Typing/inferの完全性や主型性ではない。

## 権威と境界
spec 6.3、inbox I-5の未完成診断treeを保持して最終写像を後置する回答、I-4の有限生成領域を参照。Yulang2は`notes/audit/x-oracle.md` C3-PARENT-NEGおよびrole-boundaries資料のmissing-child結果を確認した。ただし新しい一般treeを実機で検証したとは言わない。
固定Form、caller Sources、tuple alias制限はcycle92のまま。invocation identity、state-dependent materialization、更新driver/K2、4分類、辞書順序は閉じない。B4の主要橋は5本のまま。
