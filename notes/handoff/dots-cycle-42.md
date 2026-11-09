# dots cycle 42 — scalar normalization absorbed by structural closure

## 状態と時間
通知: 2026-11-09T15:27:19Z。実着手: 15:32:22Z。最新 integration/m1-final は 3511e25a4、ACTIVE・上限なし。前回cycle41 completed心拍と報告があり、稼働プロセスなし、ローカル/公開tree一致を確認。復旧不要。integrationをローカルにmergeした。

## 部分目標
有向scalar伝播と構造閉包を別の競合する観測処理にせず、scalar処理が構造閉包に吸収されることを、実関連型batch出力の診断treeまで示す。**この比較の部分目標は閉じた**。時間を埋める追加補題は作らず、検証・公開で区切る。

## 定理（全て CommonRoleScalarStructuralAbsorption）
Sは実構造正規化、Dは実有向scalar正規化。以下は任意n・State n・任意assignmentを量化する。registry、source順、tableは比較間で同じものに固定。

- `directed_derives`（補助/完全性）: 任意State s、scalar fact fについてDirectedBounds.Derived s fなら、そのatomは構造規則Derives s.atomsから導出可能。
- `directed_subset`（補助）: 任意atom xについてx∈D(s).atomsならx∈S(s).atoms。
- `structural_after_directed` / `directed_after_structural`（完全性/補助）: 全atom xについてS(D(s))、D(S(s))それぞれの所属はS(s)への所属と同値。モデル存在前提なし。リストの構造的等式ではない。
- `structural_evidence`（健全性）: 任意slot i・base bについて、その上下両方のscalar境界が独立DerivedならS(s)はiのb証拠を持つ。
- `materializes_int`（健全性）: 上記b=intかつsのモデルassignmentがあるなら、S(s)のiは実materializerでintになる。
- `models_pre` / `models_post`（健全性・完全性）: 全assignmentについてS(D(s))、D(S(s))のモデル性はsのモデル性と同値。モデル存在前提なし。
- `endpoint_pre` / `endpoint_post`（補助）: sのモデルを明示前提に、任意Endpointの評価がscalar前置/後置でS(s)から変わらない。
- `candidate_pre` / `candidate_post`（補助）: 同モデル前提の下で任意SourceRequest・DeclarationのCandidateが同値。
- `tree_pre` / `tree_post`（補助）: 同モデル前提の下で任意registry/root/tableに対する順序付き診断tree全体が等しい。
- `self_output_models_pre` / `self_output_models_post`（健全性・完全性）: 任意registry/root、AssocEnv、RoleDecls、core WellFormed証拠、全route/declarationに対するannotations、seed、table、assignmentについて、実関連型batchの生成後にDをSの前または後へ挿入しても、実StructuralGlobalChoices.outputのモデル集合は変わらない。Stable前提も整合性前提も不要。
- `self_tree_pre` / `self_tree_post`（補助）: 同じ全入力について、**生成されたraw batch出力のモデル**を明示前提とすると、前後へのD挿入は実自己出力診断tree全体を変えない。seedのモデルだけでは足りない。

## 未達とB4
一般B4の5橋は依然残る。既存Endpointはint中心の断片。raw D(s)とS(s)の等式・同値、入力batch生成前へのD挿入、role feedback反復、旧Stableと新Stableの同値を主張しない。解の存在・主型性、sourceからのannotation生成・網羅性、状態依存receiver、全意味的部分型完全性、role feedback停止、言語最終分類は未達。specの変更・意味論判断なし。新質問ノートなし。
次候補: (1) source/receiver生成と計算carrierの接続、(2) feedback driver停止と意味的閉包、(3) 独立診断分類。今回の結果は正規化部品の統合であり、B4完成ではない。

## Yulang2照合
work/dots-auditを読取りfetchし、x-oracle-types-details.md X13〜X17を読んだ。共有区間・入れ子の局所例と一般外側入口の未照合を区別。既存spec/04-typesと6.5の規則を変更していない。新実機照合なし。

## 検証
`cd lean && lake build --wfail Yulang.CommonRoleScalarStructuralAbsorption`
`lake env lean --trust=0 /tmp/cycle42-audit.lean`
327 jobsと18定理監査PASS。全体build・全Audit・verify-lean.shは指示どおり未実行。新主要定理をAuditへ登録。既存Leanファイルはroot import/Audit/README追記のみ。

~~~text
Build completed successfully (327 jobs).
BUILD_EXIT=0
'Yulang.CommonRoleScalarStructuralAbsorption.directed_derives' depends on axioms: [propext]
'Yulang.CommonRoleScalarStructuralAbsorption.directed_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.structural_after_directed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.directed_after_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.structural_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.materializes_int' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.models_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.models_post' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.endpoint_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.endpoint_post' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.candidate_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.candidate_post' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.tree_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.tree_post' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.self_output_models_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.self_output_models_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.self_tree_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleScalarStructuralAbsorption.self_tree_post' depends on axioms: [propext, Classical.choice, Quot.sound]
AUDIT_EXIT=0
~~~

## 公開・制限
個別blob作成後SHA tree・commit・非force expected-head付きref更新で一括公開。対象7ファイル。公開後remoteとlocal全treeを比較する。読取りレビューで問題なし。中断・承認待ちなし。最初の心拍updatedを時計取得前に手入力して約38秒先にした誤りあり。完了心拍は実時計から生成。空き開始49GB、終了49GB。使用量枠不明。最終公開照合時刻は親への最終報告に記録。
