# Cycle37: recursive same-head structural conflict certificates

## 開始・基点・部分目標
通知11:57:19Z、実着手11:56:57Z（環境時計の値をそのまま記録）。integration/m1-final@83dc9e12bを取得。前回work/dots-main@8d42fd161のcompleted心拍とcycle36報告を確認、復旧不要。
前回報告と心拍の統合衝突は監督役版を優先。開始心拍c8abc621dを公開してfetchし一致確認。作業場yulang一つ、空き49GB。

部分目標: pair・arrow・variant の同head内部へ再帰する矛盾証拠を、実ordinary atomsの有向変数pathを介した検出と自己出力モデル保存枝刈りまで閉じる。達成。
既存Commonのpair/arrow/variant inversion、spec/04-types.mdの構造型とspec/06-roles.mdの従来方針に沿う。意味論は変更していない。取得済みY2資料のみ参照し、最新audit再取得・新実機照合は未実行。

## 定理（全量化・前提）
以下、αは任意の変数型、l,r等は任意の実TyTerm α、ρは任意のassignment α→Comp Common.model。
### CommonRoleRecursiveConflicts
- refutes_no_subtype: 独立帰納判断Refutes l rがあれば、ρで評価したlはrの部分型ではない。Refutesは外側head不一致、pair成分、arrow引数反変/結果共変、同tag variant payloadの再帰からなる。
- fuel_sound: 任意自然数kについてcheckFuel k l r=trueならRefutes l r。
- weight_positive: 任意tの構造weightは正。
- fuel_complete: Refutes l rかつweight l+weight r≤kならcheckFuel k l r=true。
- check_exact: 内部weight和を使うcheck l r=true iff Refutes l r。外部fuel前提なし。
- checked_no_subtype: check=trueなら任意ρに対して部分型でない。
- nested_pair_checked/nested_pair_old_mismatch_false: 任意payload a,bに対しpair(int,a)≤pair(bool,b)は新check=true、旧outer mismatch=false。
- arrow_contravariant_checked: 任意payload a,bと4つの任意rowについて、arrow(bottom,a)≤arrow(int,b)は引数反変のためcheck=true。

### CommonRoleRecursivePaths
以下nは任意自然数、atomsは実Atom(Fin n)の任意有限リスト、aは任意assignment。
- recursive_exact: 上記の再帰check iff Refutesの再掲。
- pairCheck_exact: 任意有限slot対pathsと実atom x,yについて、pairCheck=true iff x=l≤i,y=j≤r、(i,j)がpathsに属し、Refutes l r。
- check_exact: pathCheck atoms=true iff 実lower/upper atomsと独立Pathによって結ばれたRefutes証拠がある。
- certificate_no_model/checked_no_model: 上の証拠またはpathCheck=trueがあれば、aはatomsのモデルでない。
- direct_exact: 任意実atom xについてdirect=true iff x=l≤rかつRefutes l r。
- check_all_exact: combined check=true iff direct証拠またはpath証拠。独立AnyCertificateとの同値。
- checked_no_model_all: combined check=trueならaはモデルでない。
- prune_models: 任意State nリストstatesとaに対し、prune後いずれかのモデル iff 元いずれかのモデル。
- nested_refutes/nested_outer_mismatch_false: 任意x,y,zに対するpair(int,x)≤pair(pair(y,z),x)の再帰証拠と旧outer検査のfalse。
- nested_chain_checked/nested_chain_no_model: 任意x,y,z:TyTerm(Fin3)について上の両端を3slotの有向経路で結んだ実atomsはcheck=true、任意aはモデルでない。

### CommonRoleRecursiveFilteredInference
全n、registry、root、env、roles、wf:WellFormed env.cores、全route/宣言のannotationリスト、seed、assignment aを量化する。
- infer_models_preserved: 新inferの出力モデル族 iff 旧path-filtered inferのモデル族。
- infer_models_exact: 新inferにaをモデルとする出力がある iff aはseedモデルで、DirectedGlobalChoices.Stable表tableが存在し、全選択route/宣言の全annotation要求とその全Computed headについてoutput slotとheadがEquivalent。
- empty_excludes_stable_model: 新inferが空で、任意tableがDirectedGlobalChoices.Stableなら、任意aはそのtableの出力モデルではない。

## 未達・次
B4主定理には依然5橋が残る。本結果は橋3/4内部の有限矛盾証拠の拡張であり、B4完了ではない。
record、effect row、union/intersection内部は再帰しない。変数で隠れた内部payloadの制約との結合、一般充足可能性、source/receiver生成、role feedback停止、言語rejected分類、X13〜X16は未達。
検出なしから充足可能性は言えない。独立Refutesに対する完全性を全Common部分型判定の完全性と混同しない。
次候補: (1)内部payload変数への制約の導出とモデル保存、(2)source/receiver生成、(3)独立な言語分類への接続。設計判断を新設していないので質問ノートなし。

## 検証
新3モジュール・25定理。root importとAudit/READMEへ追記。既存証明は変更していない。
ELAN_HOME=/workspace/scratch/1d0b4aaa3394/elan、binをPATHに設定。
`lake build --wfail Yulang.CommonRoleRecursiveFilteredInference`: exit0、322jobs。
`lake env lean --trust=0 /tmp/cycle37-audit.lean`: exit0、25定理、標準3公理のみ。
初回にはBool補題の参照方法と回帰pathの中間slot推論が失敗。明示化し再検証した。
独立読み取りレビューは問題なし。全体build・全Audit・verify-lean.shは指示に従い未実行。

### 最終出力全文
~~~text
Build completed successfully (322 jobs).
BUILD_EXIT=0
'Yulang.CommonRoleRecursiveConflicts.refutes_no_subtype' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveConflicts.fuel_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveConflicts.weight_positive' depends on axioms: [propext]
'Yulang.CommonRoleRecursiveConflicts.fuel_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveConflicts.check_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveConflicts.checked_no_subtype' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveConflicts.nested_pair_checked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveConflicts.nested_pair_old_mismatch_false' depends on axioms: [propext]
'Yulang.CommonRoleRecursiveConflicts.arrow_contravariant_checked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursivePaths.recursive_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursivePaths.pairCheck_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursivePaths.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursivePaths.certificate_no_model' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursivePaths.checked_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursivePaths.direct_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursivePaths.check_all_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursivePaths.checked_no_model_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursivePaths.prune_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursivePaths.nested_refutes' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursivePaths.nested_chain_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursivePaths.nested_outer_mismatch_false' depends on axioms: [propext]
'Yulang.CommonRoleRecursivePaths.nested_chain_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursiveFilteredInference.infer_models_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveFilteredInference.infer_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveFilteredInference.empty_excludes_stable_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
AUDIT_EXIT=0
~~~

## 公開・制限
work/dots-mainのみへ個別blobからSHA treeを一括・非force・expected-head更新。公開後に取得treeを照合する。
使用量枠は不明。中断・承認待ちは現時点なし。部分目標が閉じたので一般source生成へ範囲を広げず終了する。
