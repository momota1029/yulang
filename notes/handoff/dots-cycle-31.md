# Yulang Lean cycle31

開始 2026-11-09T06:58:01Z。integration/m1-final@f54c7bd02 の最新 standing orders/inbox を再取得。ACTIVE・上限なし、前回30 completedと報告を確認。同一作業場を再利用。統合時の報告30・心拍の衝突は統合版優先で解消。

## 部分目標
実関連型batch出力を有限scalar証拠で正規化してから、全候補表・兄弟経路を再検証する診断入口へ接続する。**この断片の部分目標は達成**。正規化を繰返したときのendpoint・candidate・順序付きtree全体の固定点も、普通制約の充足モデルを明示前提に証明した。一般role feedbackの固定点ではない。

## 定理と前提
D=CommonRoleNormalizedDiagnostic、G=CommonRoleNormalizedGlobalChoices、C=CommonRoleNormalizedDiagnosticCheck。全26定理。D/Gは任意のslot数nを量化。Gは任意の検査済みregistry、source root、env/roles、core wellformedness、外部annotation関数、seedを量化。直接双方向変数辺のscalar閉包のみ。source生成・状態依存receiverは入力の外。

### D（6定理）
- materialize_exact: 任意s,i,a、aがsのモデルなら、正規化後iがintと観測される iff 入力sからint証拠が独立導出される（健全性/完全性、断片）。
- endpoint_derived: 任意s,tと全slotのint導出同値、各々の充足モデルa,b、任意endpointについて、正規化後の観測が等しい（補助）。モデル集合同値だけを仮定しない。
- endpoint_fixedpoint: 任意sとその充足モデルa、任意endpointで二度正規化と一度正規化の観測が等しい（閉包補助）。
- candidate_fixedpoint: 同前提、任意source requestと宣言で二度/一度正規化のCandidateが同値（閉包補助）。
- tree_fixedpoint: 同前提、任意registry/root/tableで二度/一度正規化の全順序付き診断treeが等しい。子の順序と重複回数も保持（閉包補助）。
- tree_derived: 任意s,tの各充足モデル、全slot int導出同値、任意left/right表の所属同値の下で全正規化診断treeが等しい（補助）。

### G（16定理）
- requests_exact: 任意table,qで実requests所属 iff 有限choiceSpace内の選択entryのannotationに所属（補助）。
- output_canonical: 任意tableで正準表のnormalized outputが元表の出力と等しい（補助）。
- output_evidence: 任意table,i,baseでnormalized出力の明示証拠 iff raw associated出力から独立scalar導出（健全性/完全性）。
- output_models_raw: 任意table,aでnormalized/raw出力の全モデルiff。Stable・充足性の前提なし（健全性/完全性）。
- check_exact: 任意tableで実検査成功 iff normalized Stable（健全性/完全性）。Stableは自身のnormalized出力上Validかつ全選択request解決。
- search_exact: 任意tableで有限探索所属 iff 実部分集合列挙所属かつnormalized Stable（健全性/完全性）。
- complete: 任意normalized Stable表は、同じ所属・同じ出力を持つ正準表が探索される（完全性）。
- search_capacity: 探索結果長≤2^(有限choiceSpace長)。外部fuelなし（停止/容量補助）。
- resolved: 任意探索表・選択entry・そのannotationで、実Computed結果が存在（解決totality、健全性補助）。
- unknown_request_excluded: 任意選択annotationのreceiverがargsBound≠0なら表は探索されない（診断証拠限定、言語拒否ではない）。
- output_models: 任意normalized Stable表とassignmentで、全出力モデル iff seedモデルかつ全選択annotationのComputed等式が成立（健全性/完全性）。
- infer_models_exact: 任意assignmentで、列挙出力にモデルが存在 iff seedモデルかつあるnormalized Stable表の全annotation等式が成立。表を外部仮定にしない（健全性/完全性）。
- searched_tree_complete: 任意探索表とそのnormalized出力treeの任意訪問routeに一意の表候補があり、その全annotationが解決（健全性/完全性補助）。
- stable_declarative: 任意table、AssocWellFormed追加前提でnormalized Stable iff normalized出力上Validかつ全選択annotationに独立宣言的導出が存在（健全性/完全性）。
- infer_declarative_models_exact: 任意assignment、AssocWellFormed追加前提でinfer_models_exactの右辺を独立宣言的導出と全等式へ置換（健全性/完全性）。
- searched_tree_models: 任意探索表とassignmentで全出力モデル iff seedモデルかつtree訪問routeの全選択annotationのComputed等式（健全性/完全性）。

### C（4回帰）
- indirect_derived/direct_derived: 固定2slotの間接/直接int等式表現の全slotでint証拠を導出。
- repaired_tree: 上記二状態について任意registry/root/tableの全normalized treeが等しい。両者に具体的なモデルがある。
- normalized_candidate_repairs: 実int leafのcandidate検査が間接入力ではfalse、正規化後true。一般定理Dの回帰であり、言語分類ではない。

## 限界・次の橋
B4の主要5橋（source boundary、generated work、飽和停止/閉包、独立最終分類、辞書健全性/観察同値）は依然未完。今回橋1/3内部の有限scalar正規化を診断入口へ接続。解の存在・一意性・主型性・X13〜16外側PROVEDは主張しない。
normalized Stableは旧Stableと同値ではない。モデルを保存しても候補観測は変わり得るため新しい診断判断として明示。探索は指数的参照実装で、言語候補選択ではない。bool/unitも証拠には含むがendpoint観測は従来int-only。直接相互辺以外の有向SCC、構造型、任意意味的含意は未達。role feedback反復の収束は未証明。
次: (1) 実状態依存receiverからannotation生成 (2) 閉包とrole再生成の有限進捗尺度 (3) 有向SCC/構造型の証拠生成。新意味論判断なし、質問ノートなし。

## Yulang2との照合
既存取得済み notes/audit/y2-claims-role-boundaries-cycle-2.md のROLE-MORE-001〜008とspec6.3を再読。旧whereの効力を新specへ移していない。本正規化の直接の実機試験はなく未照合。最新audit再取得・新実機照合は未実行。

## 検証と制限
ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elan、PATHを設定。
`cd lean && lake build --wfail Yulang.CommonRoleNormalizedDiagnosticCheck`: exit0、313 jobs。
`lake env lean --trust=0 /tmp/cycle31-audit.lean`: exit0、全26定理。標準三公理のみ。
全体build・全Audit・verify-lean.shは常設指示に従い未実行、全体PASSとは報告しない。
初期checkで名前空間とiff書換え不足を修正。全入口をdecideで計算する回帰は経路収集の還元で停止したため、一般exactness定理を維持したうえで具体回帰をcandidate検査へ限定した。未検証コードなし。読取りレビュー問題なし、独立buildではない。
空き開始19GB。使用量枠は不明。公開前のgit diff --check成功。

### 最終検証出力全文
~~~text
Build completed successfully (313 jobs).
'Yulang.CommonRoleNormalizedDiagnostic.materialize_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnostic.endpoint_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnostic.endpoint_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnostic.candidate_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnostic.tree_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnostic.tree_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.output_canonical' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.output_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.output_models_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.search_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.search_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.resolved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.unknown_request_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.infer_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.searched_tree_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.stable_declarative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.infer_declarative_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleNormalizedGlobalChoices.searched_tree_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleNormalizedDiagnosticCheck.indirect_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnosticCheck.direct_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnosticCheck.repaired_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNormalizedDiagnosticCheck.normalized_candidate_repairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
~~~

## 公開
自身10変更ファイル（新Lean3、root/Audit/README3、design/index2、report/heartbeat2）。統合版差分を含む全treeを個別blob→小さなSHA tree→非force・expected-headでwork/dots-mainだけへ一括公開。公開後remote treeを取得して全差分を照合する。開始心拍のupdatedは手記入、最終心拍は実時計から取得。
