# Yulang Lean cycle28

開始 2026-11-09T05:28:17Z（通知05:27:19Z）。integration `c5b7a7d67` を取得し、standing orders/inbox I-12まで再読。ACTIVE・上限なし。前回completed心拍と報告を確認。同一作業場/キャッシュ使用。integration取り込み時の報告/心拍2件の衝突は統合版を優先。既存Leanの意味変更なし。

## 部分目標

**全解決証拠を、未解決の子も消さない実再帰診断treeへ接続し、独立な到達経路と訪問の同値、全関連型等式のモデル同値まで閉じる。** 有限source断片内でこの部分目標を達成。

Treeはfull ancestor route、表が有効にした候補の列、子Treeの列を格納。任意の部分表と固定観測状態で構成でき、全子成功を前提にしない。独立Representsは候補/childの所属同値と各childの再帰的正しさ。内部深さはsourceWeightから計算し、Paterson検査済宣言の各childの厳密減少で切捨てがないことを証明。外部fuel/Acc/閉包仮定は不要。

## 定理一覧（量化・前提・効く側）

D=CommonRoleDiagnosticTree、C=CommonRoleDiagnosticTreeCheck。
Dの一般定理は任意の自然数n、Paterson検査済registry、SourceRequest nのroot、有限候補表table、ordinary観測状態observationを量化。routeは完全祖先履歴つきsource node。対象は既存int-only/unary/capture-bearing有限断片であり、一般source構文ではない。

- D.build_route: 全fuelとroute rで、構築treeのroot routeはr。（補助）
- D.build_candidates: 全fuel,r,dで、構築rootの候補所属 iff 登録済d・表に(r,d)所属・独立Candidate。（健全性/完全性補助）
- D.children_edge: 全r,tで、計算された子route所属 iff 独立Edge。Edgeは登録済候補・表所属・独立Candidate・source子を要求。（健全性/完全性）
- D.edge_decreases: 全Edge r tで子のsourceWeightが親より小さい。（停止補助）
- D.build_represents: 全fuel,rでsourceWeight(r)≤fuelなら構築treeは独立Representsを満たす。（健全性補助。内部入口でboundを解消）
- D.diagnose_represents: 任意入力の内部深さで作った全treeはRepresents。（健全性補助、外部boundなし）
- D.visit_edge: 任意treeのRepresents、treeでのr訪問、Edge r tがあればtも訪問。（完全性補助）
- D.visit_path: 任意Represents tree、tree rootの独立Path、r訪問があればPath r。（健全性補助）
- D.diagnose_visit_exact: 全rで構築全treeのr訪問 iff 独立Path r。（健全性/完全性）
- D.valid_tree_total: Valid表と任意の構築tree訪問rで、表に(r,d)を持つdが存在。（補助。Validは明示前提）
- D.unresolved_child_retained: 親rのPath、登録済d、表の(r,d)、独立Candidate、任意source子c、子の表選択不在を前提に、拡張routeはtree内に残り、選択不在も保持。（健全性補助。言語分類ではない）
- D.searched_tree_complete: さらに任意AssocEnv/RoleDecls/core WellFormed、route/declarationごとのannotation写像、seedを量化。実Stable探索に所属するtableの自己出力treeを訪問する任意rに、一意な表候補dがあり、その全annotation qにはComputed出力headが存在。（健全性補助。探索所属前提、存在保証なし）
- D.searched_tree_models: 前項の探索所属と任意assignmentを前提に、自己出力のモデル iff seedのモデルかつ全visited r・表内d・その全q・全Computed headに対応する等式を満たす。annotationは外部入力で、Treeの格納payloadではない。（健全性/完全性）
- C.missing_child_after_narrowing: 既存の具体的capture親だけの部分表とordinary narrowing後の状態について、選択のない子が実treeに残る。（回帰）
- C.partial_not_valid: その部分表は強い全域証拠Validではない。部分診断treeが存在することと全解決証拠は異なる。（境界/回帰）

主型性の定理なし。部分表/全域表は診断証拠で、言語の受理・拒否範囲を定義しない。

## 限界・残り5橋

Treeは表が有効にした候補だけを記録し、全ての言語候補を分類しない。所属レベルexactnessであり、順序/重複回数の辞書同値は未達。同一parent/candidate/childの重複occurrenceは既存carrierでは区別しない。annotation/receiverは外部入力。source lowering、状態依存receiver、表・解の存在/一意性、主型性、言語の候補選択、反復driverの停止/固定点、dictionaryの観察同値は未証明。
一般B4は依然5主要橋: source boundary、全generated work閉包、飽和停止/意味閉包、独立最終分類、辞書健全性/順序同値。今回は橋4内部のchildを保持する診断証拠を閉じたが、最終言語Classifyへは接続していない。外側X13〜X16のPROVEDは未達。
次の候補: (1)source注釈生成と受け手網羅性、(2)反復driverの有限観測表現と停止、(3)source occurrenceを区別する順序/重複つき辞書解釈。
新たな意味論選択はせず、新質問ノートなし。cycle24の問いを継続。

## Yulang2照合

取得済み `y2-claims-role-boundaries-cycle-2.md` ROLE-MORE-001〜005 とspec6.3を再読。旧whereの効力は新specと異なる。今回のtableは言語選択ではなく、その差を勝手に埋めない。監査自動実行は停止中で、過去のaudit枝読取り拒否を回避しないため、最新audit再取得/新たな実機照合は未実施。

## 検証と制限

`cd lean && lake build --wfail Yulang.CommonRoleDiagnosticTreeCheck`: exit0、307 jobs。
`lake env lean --trust=0 /tmp/cycle28-audit.lean`: exit0、15定理、標準三公理のみ。
全体lake build・全Audit・verify-lean.shは指示に従い未実行。全体PASSを主張しない。
読取りレビューで論理欠陥なし。Treeのannotationは外部入力という文章を明確化して再ビルド。禁止構文なし。git diff --check成功。空き開始19GB、キャッシュ複製なし。使用量枠不明。

### focused build・監査全文
```text
✔ [306/307] Built Yulang.CommonRoleDiagnosticTree (1.1s)
✔ [307/307] Built Yulang.CommonRoleDiagnosticTreeCheck (943ms)
Build completed successfully (307 jobs).
'Yulang.CommonRoleDiagnosticTree.build_route' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.build_candidates' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.children_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.edge_decreases' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.build_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.diagnose_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.visit_edge' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.visit_path' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.diagnose_visit_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.valid_tree_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.unresolved_child_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.searched_tree_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTree.searched_tree_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticTreeCheck.missing_child_after_narrowing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDiagnosticTreeCheck.partial_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 公開

9ファイル（新Lean2、root/Audit/README追記3、design/index2、report/heartbeat2）。個別blob後の小さいSHA tree/commitと、非force・expected-head付き更新でwork/dots-mainだけへ一括公開。照合結果・実際の終了時刻は公開後に報告する。部分目標が閉じ、検証が通ったため時間埋めの追加はしない。
