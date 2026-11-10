# Cycle62: general source-named interval batch reconciliation

## Result and exact boundary

**部分目標は閉じた。** 任意の有限な source 名つき区間需要について、旧需要を保持し、旧→新・新→旧・新→新の比較だけを追加する増分 driver を定義した。その生成制約の全モデルは、元の全履歴に対する独立な「同じ source 名の全区間を同時に満たす型が存在する」という判断と iff になる。既存の `TyTerm` 全構文を量化し、positive-string / unary-int 断片へ制限しない。端点と既存の type/row slot はそのままで、実行版に中央の型を選ばせたり、新しい中央 slot を置いたりしない。

さらに、元の有限需要列が permutation なら、batch 境界・順序が違っても実 driver のモデル集合が一致する。既存 ordinary 制約を保持したまま、既存 shared presence constraint graph compiler のモデルと、元の endpoint assignment への literal readback を通した双方向を証明した。

これは**区間制約の生成とコンパイルの部分目標**である。source 名は区間需要の grouping key、端点の型・行変数は ambient assignment の別の引数である。general declarations からその需要を生成したことや、source 名を既存 graph node の canonical root に結びつけたことは主張しない。`CommonPresenceConstraintGraph` は ordinary 制約の compiled graph であり、前サイクルの `CommonRoleRegularGraph` inspection storage と同一の定義ではない。state-dependent materialization、一般 ordinary solver の完全性、飽和、四方向の分類、辞書順序、X13〜X16 の外側入口は未達。

## Theorems and which side they support

新 module: `lean/Yulang/CommonRoleSourceIntervalBatches.lean`。11定理を `Audit.lean` に登録し、`Yulang.lean` に import した。いずれも B4 の source/interval 生成橋に効く補助であり、M1 全体の健全性・完全性・主型性を主張しない。

- `arguments_exact`（補助）: 任意の source 名・有限需要列・区間について、その名の抽出リストへの所属は、元の列に同じ名と区間を持つ需要が存在することと同値。
- `cross_exact`（生成の健全性・完全性）: 任意の ambient assignment と二つの有限需要列に対し、生成した cross atoms がすべて成り立つ iff、両列の任意の同名需要の lower と upper が部分型関係にある。
- `generate_exact`（生成の健全性・完全性）: 任意の assignment・有限需要列に対し、全生成制約を満たす iff、全 source 名について、その名を持つすべての元区間を同時に満たす数学的型が存在する。consistency・選んだ witness の前提は無い。
- `step_exact`（生成の健全性・完全性）: 任意の assignment・旧需要列・新需要列に対し、旧生成制約と三方向 delta を満たす iff、結合した元需要列の独立モデル。旧/新の両方向が必要。
- `advance_exact`（補助）: 任意の assignment・state・新需要列について、state の atoms と元需要モデルの iff を前提に、一回の executable advance が同じ invariant を保つ。これは名前つき invariant を前提に持つ中間補題。
- `run_requests`（補助）: 任意の state・有限 batch 列について、driver の保存する需要は旧需要 ++ 元 batch の flatten に等しい。
- `run_exact`（生成の健全性・完全性）: 任意の assignment・初期需要列・有限 batch 列に対し、実 driver の全 atoms の成立と、元の結合履歴の独立モデルが iff。上の invariant は start から構成され、外部前提として要求しない。
- `models_perm`（補助）: 任意の assignment と二つの需要列について、列の permutation を前提に独立モデルが iff。
- `run_order_independent`（補助）: 任意の assignment、二つの初期列・batch 列について、元の結合履歴の permutation を前提に実 driver のモデル集合が iff。最終辞書の順序独立ではない。
- `compile_run_exact`（生成/コンパイルの健全性・完全性）: 任意の有限 slot 数・既存 ordinary atoms・初期需要・有限 batch・元 assignment に対して、既存 atoms と独立履歴モデルの成立 iff、compiled graph に同じ元 assignment を文字どおり readback するモデルが存在する。元の行も保持する。
- `compiled_reflects`（コンパイル健全性）: 同じ任意の入力に対し、任意の row assignment と任意の compiled graph model から、readback が既存制約と独立な元需要モデルを満たす。コンパイラが選んだ witness だけでなく全 graph model を量化する。

拒否範囲の新しい仕様判断は無い。定理は生成境界に限定し、その範囲を docstring に記した。既存定理や意味論を弱めていない。

## Verification

検証済み local source commit: `c464bd16ea2568566709d59943997a38e8af1b71`。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleSourceIntervalBatches` — exit 0。background job と bounded wait で実行。

```text
✔ [95/95] Built Yulang.CommonRoleSourceIntervalBatches (551ms)
Build completed successfully (95 jobs).
```

初回はこの環境に無い proof tactic と iff の括弧不足、次に theorem application の引数不足で失敗した。すべて証明 term を修正し、定理の型は弱めず、最終 source で再実行した。

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle62-audit.lean` — exit 0。11定理の公理監査に加え、下記3つの executable-list regression を実行した。

```text
'Yulang.CommonRoleSourceIntervalBatches.arguments_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.cross_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.generate_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.step_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.advance_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.run_requests' depends on axioms: [propext]
'Yulang.CommonRoleSourceIntervalBatches.run_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.models_perm' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.run_order_independent' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.compile_run_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceIntervalBatches.compiled_reflects' depends on axioms: [propext, Quot.sound]
```

全11定理で propext / Quot.sound のみ。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。出力全文:

```text
verify-lean: . @ c464bd16ea (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` — exit 0。

**全体の lake build、全 Audit、広域 AxiomGate は実行していない。** focused 成功を全体 PASS としない。2026-11-10T02:07:59Z の exact source commit `897faa4f48182752cb7258c77696088b030ae02d` の GitHub checks は proof/core とも in_progress。完了はこの報告作成時点で未確認。監督役の全体検証が残る。

### Reproducible focused regressions

次のコードを新 module の import に続ける。全て definitional reduction の証明で通過した。

```lean
import Yulang.CommonRoleSourceIntervalBatches
open Yulang Yulang.CommonRoleSourceIntervalBatches
open Yulang.Core.PresenceGeneration
-- Same source, two separate batches: both cross comparisons are necessary.
example : (run (start ([(7, (.base .int, .base .int))] : List (Demand Nat)))
    [[(7, (.base .str, .base .str))]]).atoms =
    [.tyLe (.base .int) (.base .int),
     .tyLe (.base .int) (.base .str),
     .tyLe (.base .str) (.base .int),
     .tyLe (.base .str) (.base .str)] := rfl
-- Equal endpoint shapes do not merge distinct source identities.
example : generate ([(7, (.base .int, .base .int)),
    (9, (.base .str, .base .str))] : List (Demand Nat)) =
    [.tyLe (.base .int) (.base .int), .tyLe (.base .str) (.base .str)] := rfl
-- Duplicate demands are retained rather than silently deduplicated.
example : (generate ([(7, (.base .int, .base .int)),
    (7, (.base .int, .base .int))] : List (Demand Nat))).length = 4 := rfl
```

## Publication and preservation

開始時の live API integration/m1-final は `604a8949ae84893f99c0fb3ffdc0f17c359c2625`。その先頭を取得し、standing orders / inbox の I-4 ACTIVE と後続 I-11 の25分上限を読み直した。前回 heartbeat は completed、cycle61 報告も公開済み。新しい crash 扱いはしない。

ローカルには cycle61 の未追跡報告・crash report と古い心拍が残っていた。これらを `/tmp/cycle62-preserved/` へ退避し、live remote の公開版を取り込んだ。衝突は心拍だけで、最新 remote を採用した。Lean source の変更や消失は無い。統合 head は作業 commit の祖先で、source tree との差分は今回の6成果パスだけ。

開始心拍は `29daf16ba53fc1066c91c87b979151eafb4e011a` に公開。成果6パス（新 module、Yulang import、Audit、README、設計ノート、設計 INDEX）と更新心拍を GitHub アプリの blob / SHA-only tree / commit API で準備し、work/dots-main のみに expected-head 付き・非 force 更新を一回行った。source 公開 SHA は `897faa4f48182752cb7258c77696088b030ae02d`、tree は `86a455922d0bfc8d0c56d1e04844c1b891d8eaef`。公開 head と完全 tree を再取得し、7変更 blob がローカルと一致、対象外2149 blob の path・mode・hash が保持されていることを確認した。大きい既存ファイルは取得した exact base に追記して blob を作り、local hash との一致も確認した。他ブランチへ書いていない。

本報告と completed 心拍を追加で公開する。本 cycle の成果・報告・心拍は計8パス。最終報告 tree も再取得して照合し、結果は完了連絡で伝える。未確認の最終 SHA をここに先取りしない。

## Timing, recovery, limits

予定開始: 2026-11-10T01:57:19Z、25分期限:02:22:19Z。作業環境での最初の date 記録は01:59:18Z。開始心拍は01:59:32Z。source の更新心拍は02:06:47Zの内容を02:07 UTC台に公開した。報告準備時刻は2026-11-10T02:09:15Z、予定開始から11.9分。I-11 に従い、部分目標が閉じた後に時間を埋めるための補題を追加しない。実際の終了は最終 completed 心拍へ記録する。

このサイクルで公開の拒否・結果不明・応答停止は無い。前回復旧の続きを再実行せず、最新 remote を基準に保全した。作業開始時と報告時の空きはともに48G（63G中13G使用）。一つの作業場と既存 cache を利用し、追加 worktree/cache copy は無い。使用量枠は不明。

## Yulang2 comparison and remaining work

実装前に work/dots-audit の x-oracle.md の X13〜X16 と C3-PARENT を読んだ。共有 source の narrowing が動機であり、今回の一般 compiler の直接の実機検証ではない。新しい Yulang2 実行はしていない。spec 6.3 と既存の centreless interval semantics を維持し、意味論の疑問を新しく決めたものは無い。質問ノートは追加していない。

B4 の主定理に残る主要橋は**5本のまま**: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound。今回閉じたのは最初の二つに必要な一般区間の生成/コンパイル部分で、state-dependent materialization 自体ではない。

次の候補は次の3点:
1. 宣言の実 interval capture から、元 source identity を保持した `Demand` を生成する橋。
2. この任意 endpoint 制約生成と、ordinary solver readout / regular inspection graph の適合を接続する橋。有限 syntax allocation と recursive endpoints の境界を明示する。
3. source 領域上で再訪・再生成を伴う driver の停止と semantic saturation。現行 batch driver は与えられた有限履歴を処理するだけで、その履歴を生成しない。

## Source CI confirmed before final publication

2026-11-10T02:09:42Z に exact source commit `897faa4f48182752cb7258c77696088b030ae02d` の GitHub checks を再確認し、core と proof が両方 completed / success だった。上記の02:07:59時点の pending 記録をこの結果で更新する。以後は報告と心拍だけの変更で、検証済み Lean source は変更していない。ローカル全体検証を実行したという主張ではない。

- core: https://github.com/momota1029/yulang/actions/runs/42740538610/job/129580187784
- proof: https://github.com/momota1029/yulang/actions/runs/42740538268/job/129580183225
