# Yulang Lean cycle43 — finite dynamic Index receiver feedback

- 開始: 2026-11-09T15:57:49Z
- 検証終了: 2026-11-09T16:05:40Z（約8分）
- 基点: integration/m1-final faee4171843ff687bf4a82730031a79a3f16035d
- 公開対象: work/dots-main のみ。変更8ファイル（新規2 Lean、design、report、既存import/Audit/README/heartbeat）。
- 前回cycle42 completedを確認し、並行実行なし。開始心拍を公開、読戻し。公開完了時刻とcommitはGit履歴が正本。
- ローカル小単位commit: 1659bb049, ee1548b1f, 43e0070ae。
- 今回は general B4 を完了していない。有限str断片の証明を進めた。

## データと実装
任意の自然数 n、State n の初期状態 s、有限スロット辺リスト edges : List (Fin n × Fin n) を入力とする。Evidence は既存の普通の上下限制約対による str 根拠。Derived はその根拠と辺に沿う伝播だけから独立に定めた判断。edges は渡された入力であり、一般ソースからの抽出は今回の成果ではない。既存の checked Index(box str) とその associated value の実評価 produceIndex を変更せず使う。

## 主要定理（省略しない前提）
以下の名前は Yulang.CommonRoleDynamicIndexClosure 内。
- [soundness/completeness] saturate_exact: 全 n,s,edges,i について、i が計算した閉包に属することと Derived s edges i は同値。
- [termination] stopped: 全 n,s,edges について、閉包上で firstFresh は none。capacity: 同じ全入力で閉包リスト長は n 以下。
- [leastness] least: 全 n,s,edges と述語 P について、全初期EvidenceがPを満たし、全入力辺(i,j)でP(i)からP(j)が従うなら、閉包の全要素がPを満たす。
- [semantic exactness] output_models: 全 n,s,edges と割当 a について、a が出力制約を満たすことと、初期制約を満たし全 Derived i の値 a(i) が str と意味的に同値であることは同値。初期モデルを全て保つという主張ではない。
- [actual producer soundness] actual_index_step: 全 n,s,edges,i,j,a について、Derived i と a が完全出力のモデルであることを仮定すると、出力状態からの実 produceIndex i j は j=str を追記した状態を返す。
- [semantic fixedness] actual_step_models_fixed: 全 n,s,edges,i,j について、(i,j)が入力辺でDerived iなら、全割当aについて、完全出力にj=strを追記した状態のモデルであることと元の完全出力のモデルであることは同値。
- [auxiliary schedule] saturate_trace: 全 n,s,edges について、閉包リストは初期根拠追加と有効辺伝播によるTraceを持つ。
- [actual execution witness] saturate_executes: 全 n,s,edges,a について、a が完全出力制約を満たすと仮定すると、閉包リストは Executed を持つ。各indexステップはその時点のrecord状態に実produceIndexを呼ぶ。最終recordは定義上outputである。初期根拠の追加は既存根拠の重複記録。整合性の存在は証明していない。
- [auxiliary exactness] record_evidence_exact: 全 n,s,xs,i について、record後のstr Evidenceは初期Evidenceまたはiがxsに属することと同値。
- [unconditional fixedness] saturate_output_fixed: 全 n,s,edges,i について、outputから同じedgesで再飽和した集合への所属は最初の閉包への所属と同値。モデル仮定なし。リスト順序や状態内重複原子の同一性は主張しない。

CommonRoleDynamicIndexExamples の regression:
- downstream_initially_pending: 3スロットの0だけstrが既知の初期状態で、実produceIndex 1 2 は none。
- final_present: 入力辺0→1→2で閉包に2が入る。
- actual_two_steps: 初期状態の実produceIndex 0 1と、その結果状態の実produceIndex 1 2がそれぞれ既存checked宣言を実行して期待状態を返す。

## 検証
既存Leanは追記許可されたimport/Audit/README以外変更なし。新規証明に未証明穴・追加公理・native評価依存なし。15定理を個別公理監査し、依存はpropext/Classical.choice/Quot.soundのみ。全体buildと全体verifyは最新inboxに従い未実行。今回の判断を全体PASSと呼ばない。

### focused build 出力全文
```text
✔ [279/279] Built Yulang.CommonRoleDynamicIndexExamples (1.1s)
Build completed successfully (279 jobs).

real	0m1.254s
user	0m0.904s
sys	0m0.413s
EXIT:0

```
### trust=0 focused audit 出力全文
コマンド: lake env lean --trust=0 Cycle43Audit.lean。監査用一時ファイルは今回の2モジュールをimportし、Audit.leanに追記した15件の#printだけを実行。
```text
'Yulang.CommonRoleDynamicIndexClosure.saturate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.least' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.record_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.actual_index_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.actual_step_models_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.saturate_trace' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.saturate_executes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexClosure.record_evidence_exact' depends on axioms: [propext]
'Yulang.CommonRoleDynamicIndexClosure.saturate_output_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexExamples.downstream_initially_pending' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexExamples.final_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexExamples.actual_two_steps' depends on axioms: [propext, Quot.sound]

real	0m1.022s
user	0m0.755s
sys	0m0.268s
EXIT:0

```

## 中断・失敗・制限
- 環境中断なし。初回regressionで決定可能性と暗黙iの推論エラーを修正後、上記buildを再実行。
- /usr/bin/time が無く、同コマンドは実行されなかった。bash組込みtimeで再実行。
- 開始心拍のelapsed_minを誤って6と書き、直後に1へ訂正した。
- work/dots-auditの新規fetchは権限審査でscope外として拒否された。再試行で迂回せず、既に取得済みの監査資料を参照。新しいYulang2実行比較は行っていない。
- str-only、有限入力辺に限る。一般source/receiver生成、任意role宣言、各状態での整合性発見、一般B4の公平再訪/停止および大域意味論の同値は未達。openを閉じたとは扱わない。
- 次の一手: 有限辺を既存source treeのIndex構文から生成し、この実行証人と接続する。一般roleの意味論を独断で追加しない。
