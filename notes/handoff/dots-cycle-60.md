# Cycle60: closure-wide allocation for actual child histories

## Result and exact boundary

**部分目標は閉じた。** 既存の unary/int materialization adapter について、単一の root と registry から構造的 closure 全体の source occurrence table を一度計算し、任意の有限 actual child history の各依存をその同じ table へ配置できることを証明した。履歴の各辺はそれぞれ独立した ordinary state を持つ。呼び出し側は有限領域への所属、選択した fuel、source 名の等式、graph adequacy を渡さない。

`actual_child_shared_allocation` は任意の有限 source table、checked registry、root/parent source request、root から parent までの actual production history、ordinary state、declaration、lower/upper type、capture depth、実 child を量化する。前提は、現状態での production 成功、head の captureDepth、実 children への所属。結論は、同じ root から延長された actual history を持つ childSource の存在、現状態での child との一致、全将来状態での有限 materializedDomain への所属である。さらに childSource の全依存 owner について、単一の global table 内に正しい child/owner entry が存在し、その source 名、旧 canonical root、任意の旧 graph・role・visible-head list に対する完全な inspection snapshot が保存される。

構造的 closure は実際の candidate 選択の上界であり、選択の完全性ではない。table は child の順序と依存の重複を保持する。constructed wrapper を新 source 変数として確保しない。一般 interval materialization、recursive syntax node の確保、旧 node の更新、飽和、一般 resolve_exact、X13〜X16 の外側入口は今回の主張に含まれない。意味論の判断や拒否範囲を追加していない。

## Theorems and role

新 module は `lean/Yulang/CommonRoleClosureSourceAllocation.lean`。以下11定理はすべて B4 の source identity/generated work に効く**補助**であり、M1 の健全性・完全性・主型性全体の完成ではない。

- `entries_exact`: 任意の registry、root、child、owner に対して、計算された entries への所属と、独立した structural Reach および child の依存への所属が同値。
- `entry_present`: 任意の global occurrence index の child は root から到達可能で、owner はその child の依存に属する。
- `dependency_present`: 任意の到達可能な child とその依存 owner について、global names table 内にその child/owner entry を持つ index が存在する。
- `owner_in_root`: 全 global occurrence の owner は root の source 依存に由来する。
- `occurrence_source`: 全 occurrence の新しい source 名は、計算された旧 owner の source 名と等しい。
- `allocated_root`: 全 occurrence の newRoot は、旧 owner の canonical root を retain したものに等しい。
- `identity_exact`: 任意の二つの occurrence は、異なる child 由来でも、旧 owner の source 名が等しい場合かつその場合だけ同じ newRoot を持つ。
- `allocated_snapshot`: 任意の table、registry、root、旧 graph、role、visible-head list、occurrence に対して、完全 snapshot は旧 canonical owner の snapshot を retain したものに等しい。
- `trace_closed`: 任意の有限 actual generation trace の終点は、root から計算された closure に属する。
- `trace_allocated`: 任意の actual trace の終点は、全将来状態で有限 materializedDomain に属し、その全依存は同じ global occurrence table 内に配置される。
- `actual_child_shared_allocation`: 上記の actual production の前提から、履歴の延長、全将来状態の領域閉包、全依存の allocation、source 名、canonical root と完全 snapshot 保存をまとめて得る。

## Verification

ローカル実装 commit は `afc80f038fdaeb05c652e814b5ba580b960c3e5c`。新 module は `lean/Yulang.lean` に接続し、11定理を `lean/Audit.lean` に登録した。検証済みの Lean ソースは公開時も同一。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleClosureSourceAllocation` — exit 0。

```text
✔ [307/307] Built Yulang.CommonRoleClosureSourceAllocation (1.2s)
Build completed successfully (307 jobs).
```

最初の試行は不要な `simpa` の lint warning で `--wfail` が失敗した。その1行を `simp` に直して再実行し、最終結果は上記のとおり。定理の型を弱めて通したものではない。

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle60-audit.lean` — exit 0。入力は新 module の import と Audit に登録した11定理の `#print axioms`。

```text
'Yulang.CommonRoleClosureSourceAllocation.entries_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.entry_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.dependency_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.owner_in_root' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.occurrence_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.allocated_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.identity_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.allocated_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.trace_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.trace_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleClosureSourceAllocation.actual_child_shared_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

依存公理は全11定理で propext / Classical.choice / Quot.sound の範囲内。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。

```text
verify-lean: . @ afc80f038f (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check` も通過。全体の lake build、全 Audit、広域 AxiomGate は実行していない。focused 検証を全体 PASS と読み替えない。2026-11-10T00:38:18Z 時点で公開 source commit の GitHub checks は proof/core とも in_progress、結論なし。Core CI と Lean inference kernel の完了は未確認。

## Publication and remote preservation

開始時の live API の integration/m1-final と work/dots-main はともに `10f8e2ddfea60e9dfeab09e237a80b33bafebf3b`。通常の branch fetch は古い mirror の head を返したため、API で確かめた exact SHA を git fetch し、作業 clone へ merge した。既存の source tree と差分が無いことを確かめており、前回成果を失っていない。orders と inbox はこの exact head から読み直した。I-4 ACTIVE と後続追記 I-11 の25分上限を適用した。

開始心拍は `5911a8a8cdfd001f907344c6cda3949d5cf94bf4`。成果6パスと更新心拍を、最新 remote tree に基づく GitHub Git-data API の一括 tree/commit 更新で `8c00dbde76ee27996a24f7c870a453b431dba203` に公開した。ref 更新は非 force、expected head 付き。tree `2088659ff03d8ccd1c5efa288851951a0f2d2a53` を再取得し、7パスの blob がローカルと一致、対象外2142 blob が保持されたことを確認した。対象外のファイルをローカルの古い内容で上書きしていない。他ブランチには書き込んでいない。

成果6パスは新 Lean module、lean/Yulang.lean、lean/Audit.lean、lean/README.md、新設計ノート、notes/design/INDEX.md。本報告と心拍を含め、本 cycle の公開対象は8パス。本報告と completed 心拍を続けて一括公開し、公開 tree を読み戻して照合する。

## Recovery, timing, and limits

前回心拍は completed で cycle59 報告も存在したため、新たな crash 復旧は不要だった。前回2回の応答停止を受け、重い検証を行わず、証明完了後に先に成果を公開した。重複書き込みなし。公開は成功応答と exact head を確認してから次へ進めた。

予定開始は2026-11-10T00:27:19Z、締切は00:52:19 UTC。前回復旧完了後の最初の時刻記録は00:30:22 UTC。報告準備時刻は2026-11-10T00:39:28Z、予定開始から12.2分、実際の開始記録から9.1分。上限内に部分目標が閉じたため、時間を埋めるための追加補題は作らない。source 公開は00:37 UTC台で、最終 completed 心拍に終了時刻を記録する。開始時・報告時とも空き48G（63G中13G使用）。既存の一つの worktree と build cache を継続利用。使用量枠は不明。

## Yulang2 comparison and remaining bridges

実装前に work/dots-audit の `notes/audit/x-oracle.md` を読み、X13〜X16 と C3-PARENT の共有source・whereの観測を確認した。これは source-level の補助証拠で、今回の numeric occurrence allocation の直接の実機検証ではない。新しい Yulang2 実行はしていない。設計は既存 spec 6.3 と前 cycle の source identity を維持し、新たな質問ノートは不要だった。

一般 B4 の未完了の橋は引き続き5本: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound。今回閉じたのは existing adapter の closure-wide occurrence allocation という部分目標で、橋全体の完成ではない。

次の候補:
1. `actual_child_shared_allocation` を一般 interval materialization/source carrier に接続し、unary/int 境界を外すための適合条件を具体化する。
2. 同じ計算済み allocation 上で、実 ordinary constraint 生成による旧 node 更新と graph inspection/source model の関係を証明する。
3. finite domain の構造的上界と実作業 driver を接続し、再訪・再生成後の意味的閉包を証明する。
