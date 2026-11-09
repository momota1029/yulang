# Cycle41: structural self-output diagnostics

## 状態・部分目標
通知13:57:19Z、実着手14:04:08Z。最新 integration/m1-final@e7f5a08d7 のstanding orders/inboxを取得。上限なし・ACTIVE、前回cycle40のcompleted心拍と報告を確認。前回稼働worker/buildなし、復旧不要。開始心拍をcf91bb62eで公開し読み戻した。開始心拍updatedを実時計より約20秒先に手入力した誤りがあったため、完了時は実時計を使う。作業場yulang一つ、空き49GB。

部分目標は、計算された構造閉包を実ordinary Stateへ戻し、自己出力探索・診断treeの再正規化不変性へつなぐこと。達成。Stateのchild/row/width証拠も保持した実行版であり、単なるatoms上の補題だけではない。完全性は新しい明示的Stable診断証拠に限定する。

## 定理の量化と前提
以下は全自然数nを量化。State nは既存のchild/width/rows構文証拠を持つ。構造分解・推移は既存規則のみ。新モジュールは2つ、定理20件。

### CommonRoleStructuralStateGrammar
- `upper_width`（補助）: 任意seed列・型term l,rでupper l=trueなら、lのwidthTailがsomeとなる場合に要求される導出を満たす（その場合が不可能であることによる）。
- `expand_good`（補助）: 任意seed・fuel・l,rについてGoodの構文と幅導出条件があれば、有限構造分解で生じる全atomもGood。
- `derived_good`（補助）: 任意State s・atom xについて、独立Derives s.atoms xならxのchild/row条件と必要なwidth制約のDerivesが成立。これによりnormalizeを本物のStateとして構成。

### CommonRoleStructuralGlobalChoices
- `normalize_models`（健全性・完全性）: 任意State s・全assignment aについて、構造正規化Stateの全atomを満たすこと iff 元のatomを満たすこと。
- `endpoint_fixedpoint`（補助・閉包）: 任意s、sを満たすassignment a、任意Endpoint eについて、二回正規化と一回正規化のe.evalは等しい。充足モデルが明示前提。
- `candidate_fixedpoint`（補助・閉包）: 同じs,aの前提で、任意SourceRequest pとDeclaration dのCandidate判定は再正規化で同値。
- `tree_fixedpoint`（補助・閉包）: 同じs,aの前提で、任意registry・root・tableについて、全順序付き診断treeは再正規化しても等しい。role生成の固定点とは違う。

以下は全registry/root、関連型env・role宣言・coreのWellFormed証拠、全route/declarationに対する入力annotations、全seedを量化する。outputは実associated batch後に構造正規化する。Stableは、その自己outputでValidな候補表であり、選択された全requestがComputedで解決すること。解の存在は前提にも結論にも置かない。

- `output_canonical`（補助）: 任意tableのcanonical代表は同じoutput Stateを返す。
- `output_models_raw`（健全性・完全性）: 任意table・assignmentについてoutputのモデル iff 正規化前batchのモデル。Stableは不要。
- `check_exact`（健全性・完全性）: 任意tableで実check=true iff 新Stable。
- `search_exact`（健全性・完全性）: 任意tableのsearch所属 iff 有限choiceSpace部分集合の列挙に属し新Stable。
- `complete`（完全性）: 任意の新Stable tableに対し、canonical代表がsearchに含まれ、全table要素所属と正確なoutput Stateが保存される。
- `search_capacity`（補助）: search長は2のchoiceSpace長乗以下。
- `resolved`（健全性）: 任意search内table、選択されたroute/declaration、そのannotation内の任意requestにはComputed headが存在。
- `output_models`（健全性・完全性）: 任意新Stable tableとassignmentについて、outputモデル iff seedモデルかつ全選択annotationのComputed head等式を満たす。
- `infer_models_exact`（健全性・完全性）: 任意assignmentについて実infer出力のいずれかのモデル iff seedモデルかつ上記全等式を満たす新Stable表が存在。全新Stable表が量化範囲。
- `searched_tree_complete`（健全性）: 任意search内tableの自己output treeの任意訪問routeには一意のtable宣言があり、その全annotationは解決する。
- `stable_declarative`（健全性・完全性）: さらにAssocWellFormedを前提に、任意tableの新Stable iff 自己outputでValidかつ全選択annotationが独立DeclarativeComputedで解決。
- `infer_declarative_models_exact`（健全性・完全性）: 同AssocWellFormed前提で任意assignmentに対し、inferのモデル族 iff seedモデルかつ自己outputでValidなtableが存在し、全選択annotationの宣言的解決が存在し、その全head等式を満たす。
- `searched_tree_models`（健全性・完全性）: 任意search内tableとassignmentについて、outputモデル iff seedモデルかつ全訪問route/table宣言に付随するannotationのComputed head等式を満たす。annotationはtree内部payloadではなく入力として参照。

## 未達と残る橋
一般B4の5橋は残る。新Stableと旧Stableの同値、解の存在・充足可能性・主型性、全意味的部分型完全性、sourceからのannotation生成・網羅性、状態依存receiver、role feedback反復停止、言語最終分類は未達。endpointの実観測は既存int中心の断片。正規化のリスト構造的冪等性とは違い、tree固定点はモデル前提付き。新しい意味論決定・質問ノートはなし。

次の候補: (1) 構造正規化と既存scalar有向正規化の比較・統合、(2) source/receiver生成への橋、(3) feedback停止・診断分類。探索の指数サイズ・carrier三乗規則生成の大入力性能は未検証。

## Yulang2との照合
今回 `git fetch origin work/dots-audit:refs/remotes/origin/work/dots-audit` は成功。最新枝のx-oracle-types-details.mdのX13〜X17を読み、構造制約・区間の局所oracleと一般外側入口の未照合を区別した。spec/04-typesと6.5に従う既存規則を変更していない。新実機実行はしていない。

## 検証
`cd lean && lake build --wfail Yulang.CommonRoleStructuralGlobalChoices`
`lake env lean --trust=0 /tmp/cycle41-audit.lean`
325 jobs、20定理のtrust=0監査成功。全体build・全Audit・verify-lean.shは指示どおり未実行。使用量枠不明。全出力は下記。

~~~text
Build completed successfully (325 jobs).
BUILD_EXIT=0
'Yulang.CommonRoleStructuralStateGrammar.upper_width' depends on axioms: [propext]
'Yulang.CommonRoleStructuralStateGrammar.expand_good' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralStateGrammar.derived_good' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.normalize_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.endpoint_fixedpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.candidate_fixedpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.tree_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.output_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.output_models_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.search_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.search_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.resolved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.infer_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.searched_tree_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.stable_declarative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.infer_declarative_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralGlobalChoices.searched_tree_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
AUDIT_EXIT=0
~~~

## 公開
個別blobを作成してSHA tree・commit・非force expected-head付きref更新でwork/dots-mainに一括公開する。完了は取得したremote treeとlocal treeの差分が空であることで確認する。対象8ファイル。初回State構成で構文証拠が不足したため専用モジュールで保持を証明して解消。中断・承認待ちなし。公開確認の実時刻は親への最終報告に記載する。

読取りレビュー済み。既存State.upper文法は右variantを許さないため、文法保持証明の同tag variantケースは到達不能。任意構造型状態への一般化ではない。最終公開準備時刻 2026-11-09T14:10:19Z。
