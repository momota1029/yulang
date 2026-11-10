# Cycle61: finite old-node updates after shared allocation, recovered publication

## Result and scope

**部分目標は閉じた。公開処理は停止していたため復旧した。** cycle60 の共有 source allocation に対して、任意の有限な旧 graph node 更新列を allocation 前後で実行した結果が graph 自体として等しいことを証明した。更新の destination と payload edge は旧 storage のみを参照する。繰り返し更新、cycle の生成・削除、knownness の変化を含め、完全な inspection snapshot が保存される。

ordinary 側では既存の positive-string solver の実際の readout で旧 storage を refresh し、source alias における string entailment と unknown の独立な元 source model による特徴づけを保持する。unary/int の actual child generator と positive-string ordinary adapter は source slot を共有するだけで、両者の型体系全体の同一性や child selection の完全性を主張しない。

## Theorems and their role

新 module: `lean/Yulang/CommonRoleAllocatedGraphUpdates.lean`。全9定理は B4 source identity / generated work の**補助**であり、M1 全体の健全性・完全性・主型性ではない。

- `write_allocate`: 任意の有限 table・suffix・旧 graph・単一旧 node edit に対し、allocation 後の lifted edit と、旧 edit 後の allocation が同じ graph。
- `run_allocate`: 任意の有限 edit list に対して同じ commutation。address の重複も許す。
- `updated_snapshot`: 任意の table・suffix・旧 graph・有限 edit list・role・旧 root・visible-head list に対し、更新後の expanded snapshot は更新後の旧 snapshot の retain と等しい。
- `actual_history_updated_allocation`: 任意の table・registry・root/child・actual generation Trace・child の依存 owner・旧 graph・有限 edit list に対し、共有計算済み table 内の child/owner occurrence が存在し、全 role・visible-head list に対する更新後 snapshot が旧 canonical owner の snapshot と対応する。Trace と owner の依存所属を前提に取る。
- `refresh_allocate`: 任意の table・suffix・original/updated graph に対し、allocated original の旧 address を updated graph で refresh した結果が updated の allocation と等しい。
- `solve_snapshot_exact`: 任意の table・suffix・initial graph・ordinary Problem・有限 Problem updates・role・source slot・visible-head list に対し、solver readout による refresh 後の完全 snapshot は、独立した元 source prepare の snapshot の retain と等しい。
- `solve_string_exact`: 同じ finite ordinary fragment の任意の table・suffix・initial graph・Problem・有限 updates・source slot に対し、string head の一致と、appendMany の Satisfies を満たす全元 source model がその slot を string と同値にすることが iff。断片内の健全性・完全性に効く補助。
- `solve_unknown_exact`: 任意の同 fragment・role・visible-head list に対し、unknown snapshot と、その source slot で値が同値でない二つの元 source model の存在が iff。
- `actual_history_solve_exact`: 任意の actual generation Trace と child の依存 owner、initial graph・ordinary Problem・有限 updates に対し、同じ共有 table の occurrence が存在し、その owner に対する string/unknown の上記 iff を満たす。generation adapter と ordinary adapter の source routing を接続するが、general declarations から ordinary updates を生成したという主張ではない。

## Verification

検証済み source commit: `0beec71a82ac6ef7b693dc267b306b520c2b1a1b`。新 module は Yulang.lean に import、9定理は Audit.lean に登録済み。保存された元の build/audit/diff の exit ファイルはいずれも0。復旧時に focused build と focused audit、diff gate を再実行した。Lean source は復旧時に変更していない。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleAllocatedGraphUpdates` — 元記録・復旧時とも exit 0。

```text
✔ [308/308] Built Yulang.CommonRoleAllocatedGraphUpdates (1.1s)
Build completed successfully (308 jobs).
```

復旧時出力: `Build completed successfully (308 jobs).`

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle61-audit.lean` — 元記録・復旧時とも exit 0。入力は新 module の import と上記9定理の `#print axioms`。

```text
'Yulang.CommonRoleAllocatedGraphUpdates.write_allocate' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.run_allocate' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.updated_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.actual_history_updated_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.refresh_allocate' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.solve_snapshot_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.solve_string_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.solve_unknown_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraphUpdates.actual_history_solve_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

全9定理で propext / Classical.choice / Quot.sound のみ。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — 元記録・復旧時とも exit 0。出力全文:

```text
verify-lean: . @ 0beec71a82 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` — exit 0。

**全体の lake build、全 Audit、広域 AxiomGate は実行していない。** focused 結果は全体 PASS ではない。公開 commit の GitHub CI 完了もこの報告作成時点では未確認。監督役が exact published source に対して全体検証する必要がある。

## Publication and preserved state

復旧時に live GitHub API と git remote を確認した。work/dots-main は `ee6edcece60572f6c68f7bd4cb36acfd363236a3`、integration/m1-final は `38eb78c25a20137fb3acd5ab79671c4e66deecef`。integration を再取得し、orders/inbox を読み直した。I-4 ACTIVE と I-11 の25分上限を適用する。最新 integration は local HEAD の祖先で、指示ファイル差分は無い。

2026-11-10T01:46:20Z の再読でも work/dots-main は上記 ee6edce のままで、停止中に ref 更新は行われていなかった。live remote tree の全2243 entry を取得して local と照合すると、cycle58〜60 の source/dependency・既存報告はすでに存在し、blob SHA が一致した。以前の復旧草稿にあった「それらも欠けていた」「19パス変更」は誤りで、ここで訂正する。公開 tree は最新 work head の tree を基に、cycle61 source・登録・設計の6パス、本報告、crash 復旧記録、completed 心拍の計9パスのみを変更する。対象外の remote ファイルと mode は保持する。blob を個別に作成した後、SHA のみを含む一括 tree/commit とし、ref は work/dots-main のみに、非 force・expected-head 付きで1回更新する。結果不明なら先に live ref を読み、重複更新しない。

公開後は exact commit/tree を再取得し、全 blob path・mode・hash を照合する。公開 SHA と照合結果は復旧完了報告で伝える。現時点ではまだ公開成功・CI成功を先取りしていない。

## Recovery, missed timing, and limits

開始: 2026-11-10T00:57:19Z。25分期限: 01:22:19 UTC。remote の最後の心拍は00:58:40 UTC、status running。local の最後の心拍は01:03:10 UTCで未公開。cycle61 report は無く、source commit も remote に存在しなかった。応答停止後に復旧担当へ引き継がれた。停止の実際の原因は未確定で、環境再起動だけに断定しない。

10分点(01:07:19)、20分点(01:17:19)の公開心拍と20分点の途中公開を実施できていない。25分上限も超過した。復旧開始の最初の確認は01:30:16 UTC、本報告準備時刻は2026-11-10T01:32:36Z、開始から35.3分。正常終了扱いにせず、遅延と欠落をここに記録する。最終 completed 心拍は復旧 publication の完了を表し、期限内完了を意味しない。

最初の復旧担当も公開準備中に応答が止まり、別担当へ再引継ぎした。再引継ぎ後の公開準備時刻は 2026-11-10T01:47:54Z、元の開始から 50.6 分。前の35.3分は報告草稿時点の値であり、最終所要時間ではない。保存済みの focused build・9定理監査の成功ログと source commit の同一性を再確認し、理論コードは変更していない。

source、設計、compiled module、検証ログは残っており、失われた source は見つかっていない。新しい理論作業や全体ビルドは追加せず、復旧公開だけを実施。復旧時の空きは48G（63G中13G使用）、/tmp は4.9G空き。元 cycle 開始時の容量は未記録。既存の一つの worktree/cache を使用。使用量枠は不明。

## Yulang2 comparison and remaining work

元の設計ノートでは実装前に既存の X13〜X16 と C3-PARENT oracle 結果を読んだと記録されている。復旧担当は新たな Yulang2 実行や独立再照合を行っていない。既存 oracle は shared source behavior の証拠で、今回の数値 address edit algorithm の直接の実機検証ではない。意味論・拒否範囲は追加しておらず、新たな質問ノートは無い。

B4 の一般主定理の未完了の橋は引き続き5本: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound。

次の候補:
1. general interval materialization と source carrier への適合条件を具体化する。
2. general declarations から actual ordinary graph updates を生成する橋と、genuinely new syntax node への edge の扱いを証明する。
3. finite source domain を実 driver に接続し、再生成と再訪後の semantic saturation を証明する。
