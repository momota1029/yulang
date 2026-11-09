# Yulang Lean cycle24

開始 2026-11-09T01:56:48Z。最新integration/m1-final `3181de1ac` をfetch。
standing orders/inbox I-11、ACTIVE、上限24を確認。cycle23 completed と報告を確認。
並行writerなし。同一作業場・キャッシュを再利用。今回が上限24の最後。

## 部分目標と結論

候補ごとのguardを保持した有限source/equation carrierを作り、first-hitが
後続候補を消す欠落をメタデータ層から除く。**この限定した部分目標は閉じた。**
任意のmask/観測状態について全有効候補のsource closureを計算し、
独立Inspectによる経路判断と、実関連型宣言の導出に対して方程式viewがexact。
候補を言語として選ぶ手続き・固定点の存在・B4は閉じていない。

3新モジュール、22定理。import/Audit/READMEに追記。既存Lean本体・spec変更なし。

## 定理と量化・前提（側）

G=CommonRoleGuardedCandidates、E=CommonRoleGuardedEquations、
B=CommonRoleGuardedCandidatesBoundary。
一般部分では全自然数n、checked registry R（Paterson検査済み）、
source root、任意source/candidate Boolean mask、任意観測ordinary state sを量化。
sourceは既存のint-only・unary・capture-bearing template断片。
全NodeはRとrootから計算した有限source領域の要素。

- G.candidate_decreases：全宣言d∈R、全parent/child、singleton候補がchildを生成すればsourceWeightが真に減る（停止補助）。
- G.candidate_in_structural：同条件でchildは計算した構造的nextに属する（領域補助）。
- G.next_exact：全parent/childで全有効候補列挙への所属 iff R内の有効候補dがそのchildを生成（健全性/完全性補助）。
- G.edge_closed：全領域内parentと生成childで、その有効候補辺があればchildも計算済み領域に属する（閉包補助）。
- G.rule_present：全Node p,cと有効候補辺について対応Horn規則が列挙される（完全性補助）。
- G.derives_sound：全Node qのHorn導出は候補辺のReachを与える（健全性補助）。
- G.derives_complete：全Node qのReachはHorn導出を与える（完全性補助）。
- G.collect_exact：全Node q、実行可能closureへの所属 iff Reach（健全性/完全性補助）。
- G.collect_capacity：全入力についてclosure長は計算した構造領域長以下（停止・大きさ補助）。
- G.candidate_child_collected：全到達parent、有効なd∈Rとその生成childについて、同じsourceを持つNodeがclosureにある（完全性補助、外部fuel/閉包前提なし）。
- E.entries_exact：全注釈写像A、Node q、宣言d、固定receiver要求rについて、(q,d,r)の保存carrier所属 iff d∈Rかつr∈A(q,d)（保持補助）。
- E.candidate_exact：全s,parent,d、singleton producerの成功 iff role一致かつ両端の独立Inspectがhit（健全性/完全性補助）。
- E.candidate_children_exact：全s,parent,child,d、候補の子への所属 iff 独立Candidateかつ宣言のsource-template子に所属（健全性/完全性補助）。
- E.reach_iff_path：全Node q、Reach iff 独立Inspectとsource置換によるCandidatePath（健全性/完全性補助）。
- E.active_exact：全entry e、Bool guardがtrue iff Reach・mask・独立Candidate（健全性/完全性補助）。
- E.activate_exact：全A,q,d,r、活性化carrier所属 iff d∈R、r∈A(q,d)、Reach、mask、Candidate（健全性/完全性補助）。
- E.retained：全A,q,d,rでd∈Rかつr∈A(q,d)なら保存carrierに属する。状態/maskによる削除なし（保持補助）。
- E.view_exact：さらに全associated env/roles、core WellFormed、注釈A、seed、assignmentについて、viewのモデル iff seedモデルかつ全Reach q・全有効候補d∈R・全r∈A(q,d)・全Computed headの出力等式を満たす（健全性/完全性補助）。
- E.view_declarative_exact：同量化に明示的AssocWellFormedを加え、右辺を独立CandidatePathとDeclarativeComputed（解決・関連型導出）に置き換えたiff（健全性/完全性補助）。

Bの3定理は上記一般結果の回帰例（補助）：
- capture_children_survive：cycle23の後続capture候補はbefore/after両状態で同じchildを持つ。
- child_collected_both：all-enabled closureはbefore/after両方でそのchildを保持。
- actual_associated_child_retained：実checked associated decoderの[0]更新後にもそのchildを保持。
主型性の新定理なし。固定例だけを単独成果とはしていない。

## 残り・意味の限定

一般B4は依然**5橋が残る**。bridge2内部の候補保持carrierのexactnessであり、
source lowering、全動的receiver、飽和停止と意味閉包、独立最終分類・辞書同値、
無条件resolve_exact、X13〜X16外側入口PROVEDは未達。
maskと観測状態、注釈は入力。言語として正しい選択を生成する定理ではない。
相容れない候補を同時に有効化した制約を言語typingとは解釈しない。
viewによる更新がguardを保つ証明もない。maskはsource-node×candidateであり、
合流した異なる祖先候補経路の相関までは保存しない。
次の候補：(1)祖先候補の相関を保つguarded carrier、(2)安定化から独立診断tree、
(3)source loweringからannotation/maskを導く橋。質問ノート1本、意味論未決定。

## 検証と制限

`cd lean && lake build --wfail Yulang.CommonRoleGuardedCandidatesBoundary` exit0、300 jobs。
`lake env lean --trust=0 /tmp/cycle24-audit.lean` exit0、22定理、標準3公理のみ。
全体lake build、全Audit、verify-lean.shは指示どおり未実行（出力・終了コードなし）。
新sorry/axiom/native_decideなし。git diff --check成功。
読取りレビューで不整合なし。経路相関の限界を追記した。

前回公開枝のmergeは心拍だけ競合したため、最新remote開始心拍を採用。
最初の検証はPATHにlakeがなくexit127、既存ELAN_HOME/binを設定して再実行し成功。
新規環境/キャッシュ複製なし。開始空き19GB。使用量枠は不明。

### Yulang2との照合

最新work/dots-auditのx-oracle X13〜X16を参照。旧実機はsurface/parser等の制限があり、
今回の内部guarded carrierを直接観測した結果ではない。新規Yulang2実行なし。
spec6.3の兄弟安定まで遅延という規則を維持し、新しい言語受理を主張しない。

### focused build 全文
```text
Build completed successfully (300 jobs).
```
### 公理監査全文
```text
'Yulang.CommonRoleGuardedCandidates.candidate_decreases' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.candidate_in_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.next_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.edge_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.rule_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.derives_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.derives_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.collect_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.collect_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidates.candidate_child_collected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleGuardedEquations.entries_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedEquations.candidate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedEquations.candidate_children_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedEquations.reach_iff_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedEquations.active_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedEquations.activate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedEquations.retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedEquations.view_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedEquations.view_declarative_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedCandidatesBoundary.capture_children_survive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleGuardedCandidatesBoundary.child_collected_both' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleGuardedCandidatesBoundary.actual_associated_child_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 公開

work/dots-main のみ、個別blob→小さなSHA tree→非force・expected-head一括公開。
10ファイル予定（Lean3、追記3、design1、question1、report1、heartbeat1）。
公開後remoteをfetchして全tree一致を照合する。最終commit・所要時間は親報告に記録。
部分目標が閉じたため、時間埋めの補題を追加せず公開へ移る。
上限24を使い切ったため、inboxの延長が無ければ次回は作業を進めない。

公開準備の個別blob API呼出しが合計約90秒を要し、10分心拍は02:07:56頃に実施
（開始から約11分、約1分遅れ）。前回の19分停止はなく、検証成果はローカル保存済み。
