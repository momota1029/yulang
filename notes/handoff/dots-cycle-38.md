# Cycle38: model-exact structural payload decomposition

## 状態・部分目標
通知12:27:19Z、実着手12:28:28Z。最新integration/m1-final@1afbae21cを取得し、前回cycle37 completed心拍と報告を確認。ローカルの報告・心拍だけ統合衝突したため監督役版を優先。作業場はyulang一つ、開始空き49GB。
部分目標は、実有向変数pathで隔てられたlower/upper端点を結合したうえでpair/arrow/同tag variantの内部payload変数を実ordinary atomsへ露出し、既存の有限path矛盾検査へ渡してモデル保存枝刈りまで閉じること。言語分類を新たに決めない。
開始心拍は98f8f8562で公開しfetchして一致確認。startedは実時計、updatedを手入力で約19秒先にした誤りがある。以降は実時計から生成する。

## 定理と前提
全て既存のCommon意味論を使う。宣言一覧は公開Leanと末尾の監査出力にもある。

### CommonRoleStructuralDecomposition
αは任意の変数型、a:α→Comp Common.modelは任意のassignment。
- expandFuel_exact: 全自然数kと全TyTerm l,rについて、有限分解後の全atomsのモデル iff 元のl≤rのモデル。燃料切れでは元atomを残すので条件なし。健全性・完全性補助。
- expand_exact: 全l,rについて内部構造weightを使った上の同値。補助。
- atom_exact: 全実atom xについて分解後の全モデル iff xのモデル。型原子と行原子を扱う。補助。
- normalize_exact: 全有限atomリストxsについて分解前後の全モデルiff。補助。
- pair_variable_exposed: 全変数iについてpair(int,i)≤pair(int,bool)はint≤int,i≤boolへ分解される。回帰。
- payload_old_check_false/payload_checked: 実1slot問題pair(int,x)≤pair(int,bool),int≤xは旧検査false・分解後true。回帰。
- payload_no_model: 上の実問題は全assignmentに対してモデルを持たない。回帰。

### CommonRolePathDecomposition
全自然数n、全実atoms:List(Atom(Fin n))、全assignment aを量化する。
- join_exact: 任意有限path対リストとatoms x,y,zについてjoin所属 iff x=l≤i,y=j≤r、(i,j)がpath対リストに属しz=l≤r。補助。
- generated_exact: 任意zについて生成リスト所属 iff 実lower/upper atomsと独立有向Pathで結ばれた端点制約である。健全性・完全性補助。
- generated_entailed: 元atomsの任意モデルは全生成制約のモデルである。健全性補助。
- normalize_exact: 生成制約を元へ追加して構造分解した結果と元のatomsは任意assignmentでモデルiff。健全性・完全性補助。
- hidden_old_false/hidden_checked: 2slot問題pair(int,x)≤y≤pair(int,bool),int≤xは直接分解だけでは検出できず、path生成後は検出される。回帰。
- hidden_no_model: 全2slot assignmentで上の実問題はモデルを持たない。回帰。

### CommonRoleDecomposedInference
全自然数n、全atoms:List(Atom(Fin n))、全a:Fin n→Comp Common.modelを量化。
- check_exact: 分解後の実checkerがtrue iff 分解後の既存独立AnyCertificateがある。一般充足可能性の完全性ではない。補助。
- checked_no_model: checker=trueならaは元atomsのモデルでない。健全性補助。
- prune_models: 全有限Stateリストについて、枝刈り後の出力モデル族 iff 元のモデル族。健全性・完全性補助。
さらに全registry/root/env/rolesとwf:WellFormed env.cores、全route/宣言からのannotationリスト、seedを量化する。
- infer_models_preserved: 新inferの出力モデル族 iff 旧RecursiveFilteredInferenceの出力モデル族。
- infer_models_exact: 新inferにaをモデルとする出力がある iff aはseedモデルで、DirectedGlobalChoices.Stable表があり、その全選択route/宣言の全annotation要求とComputed headについてoutput slotとheadがEquivalent。健全性・完全性補助。主型性・Stable存在は含まない。
- empty_excludes_original_model: 新inferが空なら、任意aについて旧inferの出力にaのモデルはない。言語rejected分類ではない。

## 未達と次
一般B4の主定理には依然5橋が残る。これは橋内部のordinary制約/診断モデル接続であり、一般B4・X13〜X16を完成したとしない。
record/effect row/union/intersectionの内部、一般充足可能性、source/receiver生成、role feedback停止は未達。全対応構造を分解し尽くす正規形性と冪等性も未証明。有限分解のモデルexactnessは燃料に依存しないが、完全なordinary solverではない。
次候補は、分解と有向closureの反復停止・閉包、source生成、独立言語分類。新たな設計判断は要らず質問ノートなし。

## Yulang2との照合
取得済みnotes/audit/x-oracle-types-details.mdを読み、X13〜X17の局所/内部区間と外側oracleの区別を維持。今回の規則はspec/04-types.mdの構造意味論とCommonのpair/arrow/variant iffに基づく。最新audit枝の再取得と新実機照合は未実行。

## 検証と制限
指定ELAN_HOMEをPATHへ追加し、focusedモジュールだけをビルド。全体build・全Audit・verify-lean.shは指示に従い未実行。
初回focused buildは編集中の分解証明を取り込んで失敗。証明の分岐を明示化した後に再実行した。独立読取りレビューで問題なし。
使用量枠は不明。公開はGitHubアプリで個別blobを作り、小さなSHA tree/commit、非force・expected-headで一括更新し、最後にfetchで全tree照合する。

## 最終検証全文
3新モジュール・21公開定理。`lake build --wfail Yulang.CommonRoleDecomposedInference` と `lake env lean --trust=0 /tmp/cycle38-audit.lean`。
~~~text
✔ [325/325] Built Yulang.CommonRoleDecomposedInference (1.3s)
Build completed successfully (325 jobs).
BUILD_EXIT=0
'Yulang.CommonRoleStructuralDecomposition.expandFuel_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralDecomposition.expand_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralDecomposition.atom_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralDecomposition.normalize_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralDecomposition.pair_variable_exposed' depends on axioms: [propext]
'Yulang.CommonRoleStructuralDecomposition.payload_old_check_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralDecomposition.payload_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralDecomposition.payload_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDecomposedInference.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDecomposedInference.checked_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDecomposedInference.prune_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDecomposedInference.infer_models_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDecomposedInference.infer_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDecomposedInference.empty_excludes_original_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRolePathDecomposition.join_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathDecomposition.generated_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathDecomposition.generated_entailed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathDecomposition.normalize_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathDecomposition.hidden_old_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathDecomposition.hidden_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePathDecomposition.hidden_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
AUDIT_EXIT=0
~~~

path生成・構造分解は一回の合成であり、反復closure/停止を完成したとはしない。部分目標は閉じたので未着手の意味論まで範囲を広げない。
