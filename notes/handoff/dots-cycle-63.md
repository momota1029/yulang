# Cycle63: original declaration heads through source capture batches

## Result and boundary

**部分目標は閉じた。** 既存の実 structural capture で捕捉できる任意有限の宣言 head / 元 goal 列について、生成した増分制約の全モデルと、元の全 head と旧 source 需要を一つの共有 source valuation が同時に満たす独立判断との iff を証明した。int / pair / tick / variable の head を構造的に捕捉し、繰り返し現れる変数の異なる元端点を残して両方向の比較を生成する。実行版は中央の型を選ばず、元端点と ordinary atoms だけを扱う。

前サイクルの「需要列の独立モデル」から、**元の宣言 head の解釈**まで意味を戻した点が今回の追加。`HeadFits` は capture・制約生成・driver を呼ばず、元 head の数学的な型が元区間に入ることを表す。公開入口 `run_satisfiable_exact` は、capture 成功や solver 成功を仮定せず、実 return と全制約の成立を、独立な有限 capture 境界と元 head モデルの連言に分ける。

範囲は明示した。source identity map と ambient endpoint slot map は別入力で、source map 自体の provenance・canonical graph root は導出していない。局所 binder の同じ綴りを自動的に同じ source と扱わない。source map が同じ名に写すものだけが共有される。元 endpoint 構文は既存 `Form` の有限構文で、前サイクルの任意 `TyTerm` 生成より入口が狭い。join head と未確定な rigid shape は structural capture の外側、role 不一致もこの generator は `none` を返す。これを言語の拒否分類とはしない。

宣言の requirements は各入力 job に保持されるが、この collector は where 子を materialize しない。繰り返し head 変数はここでは区間として照合するが、既存 candidate scanner の supported grammar を変更していない。一般候補選択・K2・state-dependent materialization・ordinary solver 完全性・飽和・四方向分類・辞書順序・X13〜X16 の外側入口は未達。仕様上の新しい拒否範囲を決めず、局所実装境界として docstring に記した。既存定理を弱めていない。

## Theorems and direction

新規 module: `lean/Yulang/CommonRoleCaptureBatchModels.lean`。13公開定理を Audit に登録し、Yulang から import。以下の「健全性・完全性」は capture/生成/compile 境界のもので、M1 全体や主型性ではない。

- `capture_fits`（健全性・完全性）: 任意の ambient/local valuation と独立な1 head capture derivation に対し、元 head の interval membership iff、全 captured binding が同じ local valuation に適合する。
- `capture_arguments_fits`（健全性・完全性）: 任意の有限 head/引数列と CaptureArguments derivation に対し、元 head 列の独立適合 iff、全 captured binding の適合。
- `capture_job_exact`（健全性・完全性）: 任意の宣言/goal/source-map job と bindings に対し、実 role 検査付き capture がその bindings を返す iff、role 一致と独立 CaptureArguments。
- `models_shared_exact`（補助）: 任意の ambient assignment と有限需要列に対し、各 source 名に共通区間要素が存在する iff、全需要を同時に満たす一つの source valuation が存在する。valuation は数学的 witness だけ。
- `demands_fits`（健全性・完全性）: 任意の endpoint slot map、ambient assignment、source valuation、job、captured bindings に対し、実 lowered demands の適合 iff、元宣言 head の適合。独立 Captures を前提とする局所補題。
- `collect_exact`（健全性・完全性）: 任意の slot map・有限 job 列・batch 列に対し、実 collector の return iff、全 job の独立 capture derivation 列。
- `captured_fits`（健全性・完全性）: 任意の captured job/batch 列と assignment/valuation について、flatten した demands の適合 iff、全元 head の独立適合。
- `run_models_exact`（健全性・完全性）: 任意の slot map・assignment・旧需要・有限 captured job/batch 列について、実 delta driver 全 atoms の成立 iff、一つの valuation が旧需要と全元 head を満たす。独立 Captured は明示した局所前提。
- `run_exact`（健全性・完全性）: 任意の slot map・assignment・旧需要・有限 job 列・出力 state に対し、実 return と state 全 atoms の成立 iff、独立 Captured batch、その batch から計算した同じ state、および共有元 head モデル。capture 成功を外部前提にしない。
- `run_satisfiable_exact`（健全性・完全性）: 同じ任意入力に対し、実 return のモデルが存在する iff、独立な有限 capture 境界が成立し、旧需要と全元 head を共有 valuation が満たす。
- `returned_models_exact`（健全性・完全性）: 任意の上記入力と実 return が示す state に対し、全生成 atoms iff、共有元 head モデル。唯一の前提は実 return で、consistency や semantic invariant を仮定しない。
- `compile_returned_exact`（生成/compile 健全性・完全性）: 任意有限 slot 数、slot map、既存 atoms、旧需要、job 列、実返却 state、assignment に対し、既存 atoms と共有元 head モデル iff、既存 graph compiler のモデルが存在し、元の type/row assignment を文字どおり readback する。
- `compiled_reflects`（compile 健全性）: 同じ任意入力と実返却 state に対し、任意 row assignment と任意 compiled graph model の readback が、既存 atoms と独立な全元 head/旧需要モデルを満たす。canonical extension だけでなく全 graph model を量化する。

## Verification

検証済み local source commit: `7b047d4d617845f6e0378e18956ee0b26ce0fc6f`。後で開始心拍を exact SHA から merge し、source commit 公開後にも exact SHA を merge した。ソース内容は変更していない。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleCaptureBatchModels` — exit 0。最終ソースで再実行。ログ:

```text
✔ [166/166] Built Yulang.CommonRoleCaptureBatchModels (607ms)
Build completed successfully (166 jobs).
```

最初の実装は subtype の model 展開と iff rewrite の透明性の違いで失敗した。小さな明示的な pair/tick の membership 補題と append 補題で証明を修正し、定理の型を弱めずに通した。最初の非待機 shell background はこの環境では保持されなかったため、以後は bounded command を background で開始して親 shell が wait する形で実行した。重い全体検証は開始していない。

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle63-audit.lean` — exit 0。13公開定理の監査と5 executable regressions。監査ログ:

```text
'Yulang.CommonRoleCaptureBatchModels.capture_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.capture_arguments_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.capture_job_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.models_shared_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.demands_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.collect_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.captured_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.run_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.run_satisfiable_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.returned_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.compile_returned_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureBatchModels.compiled_reflects' depends on axioms: [propext, Classical.choice, Quot.sound]
```

許容された propext / Classical.choice / Quot.sound のみ。Classical.choice は数学的な共有 valuation の存在証明に使われ、実行可能な collector/driver が witness を選ぶものではない。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。全文:

```text
verify-lean: . @ 7b047d4d61 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` — exit 0。

**全体 lake build・全 Audit・広域 AxiomGate は実行していない。** focused 成功を全体 PASS と呼ばない。exact published source commit の CI は下の最新確認を参照。

### Reproducible regressions

監査で通した定義と5例。最後に上記13の `#print axioms` を追加した。

```lean
import Yulang.CommonRoleCaptureBatchModels
open Yulang Yulang.CommonRoleCaptureBatchModels
open Yulang.Core.PresenceGeneration
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleSourceIntervalBatches (Demand)

def job (sourceName : Nat) (lower upper : Form) : Job :=
  ⟨⟨1, 0, [.var 0], []⟩, ⟨1, [(lower, upper)]⟩, fun _ => sourceName⟩

-- Both cross comparisons are emitted between separate captures of one source.
example : ((run id [] [job 7 .int .int, job 7 (.var 1) (.var 2)]).map
    (fun state => state.atoms)) = some
    [.tyLe (.base .int) (.base .int), .tyLe (.base .int) (.var 2),
     .tyLe (.var 1) (.base .int), .tyLe (.var 1) (.var 2)] := rfl
-- Identical local spelling in unrelated source scopes does not alias.
example : ((run id [] [job 7 .int .int, job 9 (.var 1) (.var 2)]).map
    (fun state => state.atoms)) = some
    [.tyLe (.base .int) (.base .int), .tyLe (.var 1) (.var 2)] := rfl
-- Repeated source binders are preserved through pair/tick structural capture.
example : captureJob
    ⟨⟨1, 0, [.pair (.var 0) (.tick (.var 0))], []⟩,
     ⟨1, [(.pair .int (.tick (.var 1)), .pair .int (.tick (.var 2)))]⟩, id⟩ =
    some [(0, (.int, .int)), (0, (.var 1, .var 2))] := rfl
-- Role mismatch returns outside this generation kernel, without issuing atoms.
example : run id [] [⟨⟨2, 0, [.var 0], []⟩, ⟨1, [(.int,.int)]⟩, id⟩] = none := rfl
-- A join head is still outside structural capture, even with equal endpoints.
example : run id [] [⟨⟨1, 0, [.join (.var 0) (.var 0)], []⟩,
    ⟨1, [(.int,.int)]⟩, id⟩] = none := rfl
```

## Publication and preservation

live API の integration/m1-final と work/dots-main は開始時ともに `9c12dd47c759ae425ae844436c89ade5620c3c74`。integration を fetch し、standing orders と inbox の I-4 ACTIVE / I-11 25分上限を再読した。前回の completed 心拍と cycle62 報告を確認し、復旧扱いにはしていない。ローカルは clean で source tree が integration と一致していた。

開始心拍 `1a6863a84c6db47fa8b9ebaddb6a795848d1c64c` を公開。git の work/dots-main branch fetch は古い remote-tracking ref を残したため、その ref を公開の基準にせず、live API head と exact SHA の fetch/merge を使った。未公開の source 変更を失わせず、競合は無し。

source 公開は GitHub App の blob / SHA-only tree / commit を使い、work/dots-main に一回の non-force / expected-head ref 更新で行った。6成果パスと running 心拍の7パス。source SHA は `85602c6fbcae52808c5ebdf396edf10ed69ef4f3`、tree は `880c63d22dedb6c8ccd319022fdcbc5ea973dcd2`。公開後に live head と完全 tree を再取得し、7変更blob の path/mode/hash が一致、対象外2152blob が保持されていることを確認。大きな Audit/README は exact remote base にローカルの追記だけを足して blob を作成し、各 hash がローカルと一致することも確認した。他ブランチに書いていない。

本報告と completed 心拍を続けて公開する。cycle 全体の対象は計8パス。最終 SHA と完全tree照合は実際に終わってから完了連絡で伝え、ここでは先取りしない。

## Time, limits and recovery

予定開始 2026-11-10T02:27:19Z、期限02:52:19Z。開始前の最初の作業環境 date は02:26:44Z、開始心拍は02:27 UTC台、source更新心拍は02:34:08Zの内容を02:35 UTC台に公開。report準備時の時刻は後述。I-11に従い、部分目標が閉じた後に時間を埋める補題は追加しない。

公開の拒否、結果不明、応答停止は無し。作業開始時と source公開後の空きは48G（63G中13G使用）。既存作業場・既存cacheを使い、worktreeやcache copyを増やしていない。使用量枠は不明。

## Yulang2 comparison and remaining bridges

実装前に work/dots-audit の x-oracle.md の X13〜X16、C3-PARENT/C3-PARENT-NEG を読んだ。source共有と兄弟要件の動機であり、この一般有限capture theoremの実機証明とは区別する。新しいYulang2実行はしていない。spec 6.3と既存interval semanticsを保持し、新しい意味論の判断や質問ノートは無い。

B4 主定理に残る主要橋は**5本のまま**: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound。本 cycle は最初の二つに必要な「既存structural captureから元head意味論への一般橋」を閉じたもので、いずれかの主橋全体が閉じたという主張ではない。

次の候補:
1. 宣言の実 materialization / canonical source node から、今回の明示的 source identity map を構成する。局所 binder 名の単純再利用で代用しない。
2. captured parentから生成される実where childが、同じsource mapと元端点を保つ橋。candidate scannerのgrammarとinterval reconciliationの差を隠さない。
3. ordinary graph readoutからinspection状態更新・再生成を経る実driverを、有限仕事領域・Paterson/K2の停止と意味的飽和に接続する。

## Exact source CI and final preparation

2026-11-10T02:37:15Z に exact source commit `85602c6fbcae52808c5ebdf396edf10ed69ef4f3` の checks を再確認し、proof/core とも completed / success だった。以後は報告・心拍だけで Lean source は変更していない。ローカル全体検証を実行したという意味ではない。

- proof: https://github.com/momota1029/yulang/actions/runs/42743820659/job/129591041031
- core: https://github.com/momota1029/yulang/actions/runs/42743820608/job/129591039688

報告準備時刻 2026-11-10T02:37:15Z、予定開始から約9.9分。completed心拍を同時に公開し、その後の最終tree照合までで終了する。
