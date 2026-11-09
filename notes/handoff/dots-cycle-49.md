# Cycle 49: independent source semantics and checked readout

## 基点・部分目標
integration/m1-final `269fdb941` を取得・統合し、standing orders と inbox I-12 まで再読。STOP なし。開始 2026-11-09T18:58:25Z。前回48の完了心拍と報告を確認し、復旧不要。同じ作業場だけを使用し、他の書き込みプロセスなし。

今回閉じた部分目標: **有限 str/equality source の独立したモデル意味論から、飽和後の実 checked producer の成功・保留を特徴づけ、成功した要求の再実行がモデルを変えないことを示す**。
当初の診断 tree への直接接続は、既存 Endpoint.eval が int または unknown のみを観測するため行わなかった。str を int に見立てたり既存の意味論を変更したりせず、先に source 意味論と読取の橋を閉じた。

## 主張と量化
新規 `lean/Yulang/CommonRoleDynamicIndexSourceSemantics.lean`。namespace は `Yulang.CommonRoleDynamicIndexSourceSemantics`。
共通して、任意の有限 source table T、seed slot リスト S、slot 等式リスト L、名前つき要求リスト R を量化する。slot i/j は T の任意の位置。空の table、重複、未到達を除外しない。SourceModel は seed の str 等式・slot 等式・同名 alias 等式・各要求の str 伝播条件からなる独立な判断。飽和・検出・出力 atoms を定義に含めない。F i は全 SourceModel が i の型を str と同値にする命題、D i は既存の独立導出、O は実飽和出力。

- `source_models_initial`（健全性）: 任意の割当 a について SourceModel a なら a は initial のモデル。
- `derived_sound`（健全性）: 全 i、D i なら F i。
- `source_models_output`（健全性）: 任意の a、SourceModel a なら a は O のモデル。逆向きは主張しない。
- `separating_source_model`（完全性の証人）: 到達位置を str、非到達位置を int とする既存の分離割当は SourceModel。外部の整合性前提なし。
- `string_source_model`（補助）: 全位置 str の割当は SourceModel。モデル集合は空でない。
- `source_forces_iff`（健全性・完全性）: 全 i、F i iff D i。
- `source_output_forcing_iff`（健全性・完全性）: 全 i、SourceModel 全体の str 帰結と O のモデル全体の str 帰結が一致。
- `checked_source_exact`（健全性・完全性）: 全 i,j、checkedProduceIndex O i j が some out となる out が存在 iff F i。要求所属を仮定しない。
- `source_underdetermined_iff`（完全性）: 全 i、i の型が非同値な二つの SourceModel が存在 iff F i でない。
- `checked_pending_iff`（健全性・完全性）: 全 i,j、checkedProduceIndex O i j = none iff i の型が非同値な二つの SourceModel が存在。不整合による失敗を混ぜない。
- `checked_request_models`（意味的閉包）: 全 i,j,out と割当 a、(source i,source j)∈R かつ checkedProduceIndex O i j=some out なら、a が out のモデル iff a が O のモデル。成功した要求の再実行は原子列の一致ではなく全モデルの保存になる。
- `output_models_not_source_models`（境界の反例）: table=[10,20]、seed/equality なし、要求10→20の固定 witness では、O を満たすが SourceModel でない割当が存在。未解決要求の条件は O の atoms に残らないため、上の一般の帰結一致をモデル集合全体の一致と読み替えられない。

これは正の str 帰結だけの断片。一般 Index payload、任意初期 State、parser/lowering、全言語の四分類、辞書同値、主型性を証明していない。名前のない要求 endpoint の検査は既存 WellScoped との接続が別途必要。仕様として不許可範囲を決めたのではなく、実装・証明断片の限定であることを module docstring と SourceModel に明記した。既存定理の変更なし。

## 検証
コマンド `cd lean && ELAN_HOME=../../elan timeout 240 ../../elan/bin/lake build --wfail Yulang.CommonRoleDynamicIndexSourceSemantics`、終了0:
```text
✔ [285/285] Built Yulang.CommonRoleDynamicIndexSourceSemantics (1.2s)
Build completed successfully (285 jobs).

```
コマンド `cd lean && ELAN_HOME=../../elan timeout 240 ../../elan/bin/lake env lean --trust=0 /tmp/cycle49-audit.lean`、終了0。新12定理の監査全文:
```text
'Yulang.CommonRoleDynamicIndexSourceSemantics.source_models_initial' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.derived_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.source_models_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.separating_source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.string_source_model' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.source_forces_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.source_output_forcing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.checked_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.checked_pending_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.checked_request_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.output_models_not_source_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```
コマンド `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`、終了0。差分検査のみの全文:
```text
verify-lean: . @ e6e061702 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

```
`git diff --check` 終了0。新モジュールを Yulang.lean に import、全12定理を Audit.lean に追記。全体 lake build・全 Audit・全体公理 gate は実行していない。全体 PASS は監督役の確認待ち。
初回の単体ビルドでは、この環境にない tactic 名を二箇所で使って失敗。場合分けと矛盾除去へ直し、最終コードの単体ビルド・監査を通した。最初の shell-background 起動は残存プロセスがなくログ空だったため、上限つきの継続セッションで実行し直した。未完の重い処理はない。

## Yulang2 との照合
最新 work/dots-audit の x-oracle X13〜X17 と spec/06-roles.md 6.3 の関連型流入・兄弟の安定時解決を確認。旧実機の表示はこの有限 source carrier の検証にはならない。新たな Yulang2 実機試験は未実施。新しい言語意味論を決定せず、質問ノートは追加していない。int-only decoder との接続制限は設計ノートに明記。

## B4 と次の仕事
一般 B4 へ残る橋は5本: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound。今回閉じたのは有限 str/equality 断片の source 帰結完全性と実 producer 読取・意味的閉包。一般形の橋が減ったとは数えない。
次の候補は (1) str を保持できる source endpoint carrier と既存診断 tree の接続、(2) 未解決要求の条件を残す出力意味論、(3) WellScoped の検査とこの独立 source 意味論の接続。

## 公開・時間・容量
検証済み実装のローカルcommit `e6e061702`、当初の報告commit `5b285708b`。開始心拍は GitHub app で公開・読戻し済み。公開先は `work/dots-main` のみ。他branchへの書き込みは行わない。

### 公開停止と復旧
- 2026-11-09T19:04:32Z（開始後367秒）の記録は、ローカル実装と検証が終わった時刻であり、サイクルの公開完了時刻ではなかった。当初のローカル心拍 `status: completed` と「中断なし・25分上限内」の記載を訂正する。
- 成果8ファイルをcontent入りの一括 `github_create_tree` で作成する処理が停止し、1,019秒後に中断した。tree objectの作成成否は不明。commit作成とbranch ref更新は実行していない。開始10分・20分の中間心拍を公開できず、公開までを含む25分上限（19:23:25Z）を超えた。
- 復旧時、前の作業担当は終了済み、書き込み中のローカルprocessなし、checkoutは `5b285708b` でcleanと確認。GitHubのbranchを再読し、headが開始心拍だけの `685fb39a6ba78063020c8d1aa3bf7c9b18e8e941` のままであることを確認した。実装の紛失はない。
- 復旧は新しい証明を加えず、個別blobを作成してSHAだけの小さなtreeにまとめ、上記headをparentにしたcommitを非force・expected-head指定で公開する。成否を確認してから、全8ファイルのblob照合と完了心拍を行う。
- この記録時点（2026-11-09T19:24:33Z、開始後26.1分）は公開復旧中。公開完了時刻・commit・照合結果は確認後に追記する。

開始時・検証終了時・復旧時の空き容量はいずれも48GB。全体ビルド・全Audit・全体公理gateは未実行のまま。使用量枠は不明。
