# Cycle36: directed structural path conflict certificates

## 基点・復旧・部分目標
通知11:27:19Z、実着手11:28:53Z。最新integration/m1-final@a335982db、前回work/dots-main@b8ef87622。
前回completed心拍と報告あり、ローカル成果も保存済み。復旧不要。統合時の前回報告と心拍の衝突は監督役側を優先して解決した。
開始心拍54dea10beを公開し取得内容一致を確認。作業場はyulang一つ、空き49GB。

部分目標は、任意payloadを持つ構造headの不一致を、実ordinary atoms中の任意長の有向変数経路を介して検出し、全自己出力モデル族を保存する枝刈りへ接続すること。

## Yulang2との照合
取得済みROLE-MORE-001〜008とspec/04-types.md、および既存CommonRigidHeadInspectionのhead分離を確認。
最新audit再取得と新実機照合は行わない。旧role候補の挙動を採用する定義ではなく、現Common部分型推移律に基づく矛盾証明である。

## 未達
一般B4は5橋が依然未完。本成果は橋3/4内部の有限矛盾証拠。
同head内部、構造のunion/intersection、一般の充足可能性、source生成、state依存receiver、role feedback停止、言語最終分類、X13〜X16は未達。
次候補: (1)同head内部の構造境界、(2)source/receiver生成への接続、(3)独立言語分類への接続。
意味論は決定していない。質問ノートなし。全体build/全Audit/verify-lean.shは指示どおり実行しない。
使用量枠は不明。

## 定理の全量化・前提と役割
CommonRoleStructuralPaths の一般定理は全自然数n、実Atom(Fin n)リストatomsを量化する。
- facts_complete/facts_length（補助）: 全slot対fは全列挙に含まれ、全列挙の長さはn*n。
- edge_exact（健全性/完全性）: 全i,jについてedge=true iff 実var i≤var j atomがある。
- reach_refl/reach_step（補助）: 全iが自分に到達、全i,j,kについて(i,j)到達と実j≤k辺から(i,k)到達。
- rules_path（健全性）: 全生成Horn ruleの全前提が独立Pathなら結論もPath。
- reach_exact（健全性/完全性）: 全i,jについて実reachへの所属 iff 独立Path。Pathは反射と実有向辺への延長から帰納定義。
- reach_capacity/reach_stopped（補助）: 全atomsについてreachの長さ≤n*n、内部閉包後のfirstFreshはnone。外部fuelなし。
- path_subtype（健全性）: 全i,jとassignment aについてPath atoms i jと全atomsのモデルaがあればa(i)≤a(j)。
- pairCheck_exact（健全性/完全性）: 任意slot対リストpaths、任意atoms x,yについてpairCheck=true iff x=l≤i,y=j≤r、(i,j)∈paths、Mismatch l r。
- check_exact（健全性/完全性）: 全atomsについてcheck=true iff 独立Certificate（l≤iとj≤rの実atoms、Path i j、外側head不一致）。
- certificate_no_model/checked_no_model（健全性）: 全atoms,aについてCertificateまたはcheck=trueならaはatomsのモデルでない。
- prune_models（健全性/完全性）: 任意State nの有限リストstates、任意aについて枝刈り後いずれかのモデル iff 元いずれかのモデル。
- chain_path/chain_checked/chain_old_check_false/chain_no_model（回帰）: 任意l,r:TyTerm(Fin3)、任意aについてpair(l,r)≤0≤1≤2≤intの実4atomsは0→2のPathを持ち、新check=true、旧check=false、モデルaなし。

CommonRolePathFilteredInference の3定理は全n,registry,root,env,roles,wf:WellFormed env.cores、入力annotations、seed、assignment aを量化する。
- infer_models_preserved（健全性/完全性）: 新inferのいずれかのモデル iff 旧structural inferのいずれかのモデル。
- infer_models_exact（健全性/完全性）: 新inferのいずれかのモデル iff seedモデルかつDirectedGlobalChoices.Stable表tableが存在し、全選択route/宣言の全annotation要求と全Computed headに対しoutput slotとheadがEquivalent。
- empty_excludes_stable_model（健全性）: 新inferが空、tableがDirectedGlobalChoices.Stableなら、任意aはそのtableのoutputモデルでない。
旧direct検出は旧filterの後に新filterを適用して保持する。一般の解の存在、主型性、言語rejected分類ではない。

## 検証と結果
部分目標は閉じた。新規2モジュール、22定理。設計から作り、既存証明は変更していない。
ELAN_HOME=/workspace/scratch/1d0b4aaa3394/elan、binをPATHに設定。
`lake build --wfail Yulang.CommonRolePathFilteredInference`: exit0、319jobs。
`lake env lean --trust=0 /tmp/cycle36-audit.lean`: exit0、22定理、標準3公理のみ。
初回にはlist長のsimpとrule destructuringが失敗し修正して最終検証を再実行した。
独立読取りレビューは問題なし（独立ビルドではない）。全体検証は未実行。

### 最終出力全文
~~~text
✔ [319/319] Built Yulang.CommonRolePathFilteredInference (957ms)
Build completed successfully (319 jobs).
BUILD_EXIT=0
'Yulang.CommonRoleStructuralPaths.facts_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralPaths.facts_length' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralPaths.edge_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralPaths.reach_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.reach_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.rules_path' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralPaths.reach_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.reach_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.reach_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.path_subtype' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralPaths.pairCheck_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.certificate_no_model' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralPaths.checked_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.prune_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.chain_path' depends on axioms: [propext]
'Yulang.CommonRoleStructuralPaths.chain_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralPaths.chain_old_check_false' depends on axioms: [propext]
'Yulang.CommonRoleStructuralPaths.chain_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathFilteredInference.infer_models_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRolePathFilteredInference.infer_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathFilteredInference.empty_excludes_stable_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
AUDIT_EXIT=0
~~~

## 公開・制限
work/dots-mainのみ、個別blobからSHA treeを一括で非force・expected-head更新する。
新Lean2、root/Audit/README追記、設計ノート/索引、報告/心拍の9ファイル。
API公開後の全tree比較を行う。コードの部分目標が閉じたため次の構造内部の橋は次サイクルに分ける。
