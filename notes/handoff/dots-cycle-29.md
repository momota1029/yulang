# Yulang Lean cycle29

開始 2026-11-09T05:56:48Z。最新integration 0d24e57ec を取得しstanding orders/inbox I-12を再読。ACTIVE・上限なし・前回completed/報告確認。報告28/心拍のmerge衝突は統合版優先。同一作業場/キャッシュ、空き19GB。

## 部分目標
診断treeの正準表現を、候補/子の所属だけでなく全リストの順序と重複を含む構造的等式へ強める。固定registry・固定source列挙順の有限断片で達成。Valid/Stable表の正準探索代表が同じ全treeを生成する。

一般のモデル同値からmaterialization同値は出ないことも発見。x=y,y=int と x=int,y=int は全assignmentでモデルが一致し充足可能だが、現直接証拠decoderは前者のxを未知にする。反例だけで終えず、実atomを検査して一つの相互変数辺と直接scalar等式を伝播する実行可能normalizeを追加。全モデル保存、充足モデルがある場合のint認識、具体反例の修復を証明。単一転送であり一般飽和/driverへ未接続。

## 定理（量化・前提・効く側）
C=CommonRoleDiagnosticCanonical。任意n、Paterson検査済registry R、SourceRequest nのrootを量化。表a,bは有限route/declaration列、s,tはState n。int-only/unary/capture-bearing断片で一般sourceではない。
- active_test_eq: 全route r・登録済d、独立ActiveEquivalent(a,b,s,t)なら実active test等式（健全性/完全性補助）。
- enabled_eq / children_eq: 同前提、全rで候補/子リストが順序/重複込みで等しい（補助）。
- build_eq: 同前提、全fuel/rで全tree等式（補助）。
- diagnose_eq: 同前提、内部深さ入口で全tree等式、外部fuel不要（補助）。
- diagnose_membership: 全a,b,s、表の全要素の所属同値から全tree等式（補助）。
- valid_canonical_tree: 全table,s、Validを前提に正準表が実探索に所属し元と同じ全tree（完全性補助、Validは明示前提）。
- endpoint_atoms: 全s,t、atom所属同値、任意assignmentのsモデルの下で全Endpoint評価が等しい（補助）。
- candidate_atoms: 同前提、全source request/declarationの独立Candidate iff（健全性/完全性補助）。
- diagnose_atoms: 表所属同値と前項ordinary前提から全tree等式（補助）。
- output_membership: 全AssocEnv/RoleDecls/core WellFormed、全route/declaration注釈写像、seedを追加量化し、表所属同値から自己出力State等式（補助）。
- self_tree_membership: 同前提で自己出力全tree等式（補助）。
- stable_canonical_tree: 全上記パラメータ、Stableな任意tableの正準代表が実探索に所属し自己出力全tree等式（完全性補助）。Stableの存在/充足性は保証しない。

B=CommonRoleDiagnosticCanonicalBoundary。Fin2上の具体的indirect/direct。
- linked_models: 全assignmentで相互変数辺のモデル iff 2変数の型同値（健全性/完全性補助）。
- same_models: 全assignmentでindirect/directモデルiff（境界）。
- consistent: 両方を満たすall-int assignmentの存在（境界）。
- indirect_unmaterialized / direct_materialized: slot0実decoderが前者none、後者int（境界）。
- endpoint_difference: 両stateのslot0 Endpointが異なる（境界）。

E=CommonRoleDiagnosticEvidenceTransfer。任意n,s:State n,i,j:Fin n,base:Inference.Baseを量化。
- edgeTest_exact: 全atomで実edgeTest成功 iff 指定var辺と等しい（健全性/完全性補助）。
- check_exact: 実check成功 iff 双方向辺とjの直接base Evidenceが所属（健全性/完全性補助）。
- transferable_models: Transferableと任意assignmentのsモデルからiの型がbaseと同値（健全性）。
- normalize_models: 全assignmentで実normalize後モデル iff 元モデル。外部Transferable/充足性前提なし、内部で実checkする（健全性/完全性）。
- normalize_evidence: Transferableからnormalize後iの直接base Evidence（補助）。
- normalize_materializes_int: base=intのTransferableと任意assignmentのsモデルから実materializerがiをint認識（健全性補助）。
- boundary_repaired / boundary_repaired_endpoint: Bの具体例を実normalizeするとslot0がint、direct側Endpointと等しい（回帰）。
主型性の新定理なし。言語受理/拒否を定義せず内部decoder境界を示す。

## 限界と残り5橋
registry/source列挙順は固定。where宣言並替え、辞書観察同値、欠けたoccurrence番号は未解決。表の並替え不変性を宣言順不変性と混同しない。normalizeは単一局所転送で、任意意味的含意・反復飽和・状態依存receiver・source lowering・最終言語選択は未達。
一般B4の5主要橋は残る: source boundary、generated work閉包、飽和停止/閉包、独立最終分類、辞書健全性/観察順序同値。今回は橋5内部の表現不変性と橋1/3に関係するdecoderの弱さ・局所修復。X13〜16の外側PROVEDは未達。
次: 有限相互変数辺の反復転送と停止/閉包、そのdriver接続、source occurrenceつき辞書同値。意味論の新選択なし、新質問ノートなし。

## Yulang2照合
取得済みROLE-MORE-001〜005とspec6.3再読。旧whereの効力は新specと異なる。今回の表を言語選択としない。最新audit再取得/新実機照合は未実施（停止済み監査権限拒否を回避しない）。Y2の辞書意味同値は証明していない。

## 検証
最初lakeがPATHに無くexit127。既存ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elan とbinを設定して再実行。
cd lean && lake build --wfail Yulang.CommonRoleDiagnosticEvidenceTransfer: exit0、308 jobs。
lake env lean --trust=0 /tmp/cycle29-audit.lean: exit0、27定理。
全体build/全Audit/verify-lean.shは指示どおり未実行。全体PASSを主張しない。標準三公理のみ。git diff --check成功。空き19GB、使用量枠不明。

### 全出力

~~~text
Build completed successfully (308 jobs).
'Yulang.CommonRoleDiagnosticCanonical.active_test_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.enabled_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.children_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.build_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.diagnose_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.diagnose_membership' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.valid_canonical_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.endpoint_atoms' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.candidate_atoms' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.diagnose_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.output_membership' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.self_tree_membership' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonical.stable_canonical_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonicalBoundary.linked_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonicalBoundary.same_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonicalBoundary.consistent' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticCanonicalBoundary.indirect_unmaterialized' depends on axioms: [propext]
'Yulang.CommonRoleDiagnosticCanonicalBoundary.direct_materialized' depends on axioms: [propext]
'Yulang.CommonRoleDiagnosticCanonicalBoundary.endpoint_difference' depends on axioms: [propext]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.edgeTest_exact' depends on axioms: [propext]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.check_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.transferable_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.normalize_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.normalize_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.normalize_materializes_int' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.boundary_repaired' depends on axioms: [propext]
'Yulang.CommonRoleDiagnosticEvidenceTransfer.boundary_repaired_endpoint' depends on axioms: [propext]
~~~

## 公開
新Lean3、root/Audit/README追記3、design/index2、report/heartbeat2の10自身変更ファイル。統合版報告28もremoteとの差分に含むので公開差分11。個別blobとSHA tree、非force・expected-headでwork/dots-mainのみ公開。照合/最終時刻は公開後記録。検証終了 2026-11-09T06:07:18Z。

### 公開照合
06:10:03 UTC、work/dots-main@610879607 をfetchしremote/local全tree差分空・clean確認。11ファイル公開（自身変更10＋統合版報告28）。中断・承認待ちなし。開始から13分15秒。開始心拍05:57、検証心拍06:04、成果06:10。全体検証は未実行。最終照合記録とcompleted心拍を追加公開する。
