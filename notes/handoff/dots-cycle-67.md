# dots cycle 67 — computed fresh capture demand sources

## Summary and scope

**部分目標は閉じた。** caller が任意に渡していた local binder の demand 名について、独立した新規 capture の場合を実計算へ接続した。実際の old demand list の全名より大きい境界を計算し、各 binder に `boundary old + binder` を割り当てる。同じ呼び出しの binder identity を正確に保ち、どの old demand 名とも衝突しない。ambient endpoint 名・root owner・compound interval の中心値を demand 名として流用しない。

単発の allocation だけではなく、**任意有限の実 child 経路**へ合成した。新しい Instruction に source map はない。driver は各段の実 return の demand list を次へ渡し、その list から次の map を計算する。`follow_models_exact` は、最終 request history にモデルが存在する実成功 iff 初期 history にモデルが存在し、各段の独立した元 head / where-template model が成立する、と証明する。すべての段で ambient assignment は同一。量化は任意の finite instruction list であり、固定した例や固定深さではない。

独立判断 `PathModels` は Accepts、元の expand の child position、元 head / where-template model だけを使う。runner、ordinary atom list、freshSource を参照しない。共通の存在 valuation を前提として与えるのではなく、old valuation と独立な local valuation から衝突しない一つの valuation を構成する。

**境界を維持:** これは新しい独立 invocation の断片。再訪を毎回 fresh にするという言語意味論を決めていない。意図した共有がある invocation は割当済み map を保持する必要がある。stable invocation key、再訪時の registry lookup、associated equality を通した共有と feedback は未接続。path は caller が選ぶ正の child 経路であり、候補の非正結果・child position 不在では path utility が停止する。これを language-visible pending / selected / ambiguous / rejected に読み替えない。

cycle66 の実 History への接続も証明し、任意 root からの実 recursive capture が ambient source 領域を保つことをそのまま使う。一般の有限 goal 領域・fairness・飽和停止・意味的閉包・辞書・外側 resolve_exact・X13〜X16 の外側入口・M1三つ組は未完。既存の structural linear interval grammar を広げていない。

## Theorems and quantified claims

新規 `lean/Yulang/CommonRoleFreshCaptureSources.lean` の15定理を全て Audit へ登録し、Yulang から import した。既存 Lean は許可されたファイルへの追記のみ。

1. `old_below`（補助）: 任意 old demand list とその任意 member について、member の名前は計算境界未満。
2. `fresh_ne_old`（補助・健全性）: 任意 old list・binder・old member について、計算された fresh 名はその old member 名と異なる。
3. `fresh_identity`（局所健全性・完全性）: 任意 old list と任意二 binder について、割当名が等しい iff binder が等しい。
4. `extend_old`（補助）: 任意 old list・previous/local valuation と old member について、構成 valuation は元の値を保持する。
5. `extend_fresh`（補助）: 同じ任意入力について、構成 valuation と fresh map の合成は local valuation と関数として一致する。
6. `extend_shared`（補助・健全性）: 任意 assignment・old list・previous/local valuation について、previous が old を満たすなら構成 valuation も old を満たす。
7. `generated_models_exact`（局所健全性・完全性）: 任意 slot map・assignment・old list・宣言・goal・bindings と実 Accepts derivation について、計算済み map を使う生成 ordinary atoms のモデル iff old のモデルかつ元 head と全 where template の独立 local model。source map・共通 valuation・子辞書成功を仮定しない。
8. `run_exact`（局所健全性・完全性）: 任意 slot map・assignment・old list・宣言・goal・result について、実正 return と生成 atoms のモデル iff 独立 accepted bindings・実結果の構造・old model・独立 local model。
9. `generated_fresh`（補助・健全性）: 任意 slot map・old list・宣言・goal・bindings・生成された任意 demand・任意 old member について、両者の名前は異なる。
10. `history_owners`（補助・健全性）: 任意実 History と任意 old list・宣言・実 fresh-run 正 return について、capture/child payload 全体の元 root owner が実計算され、全名列の順序・重複と正準性を保つ。
11. `generated_requests_exact`（局所健全性・完全性）: 任意 slot map・assignment・old list・宣言・goal・bindings について、生成 state の atoms のモデル iff 同 state の実 request history のモデル。Accepts やモデル存在を前提にしない。
12. `next_exact`（局所健全性・完全性）: 任意 slot map・assignment・開始/終了 cursor・instruction について、実一段 descent 成功と終了 history のモデル iff 独立 accepted bindings・選んだ実 child position・実生成 history の一致・開始 model・元 local model。
13. `follow_models_exact`（局所健全性・完全性）: 任意 slot map・assignment・cursor・有限 instruction list について、モデルを持つ実成功終了 cursor が存在する iff 初期 history のモデルかつ独立 PathModels。任意深さに対応し、成功・深さ・source map の前提はない。
14. `next_history`（補助・健全性）: 任意 root と到達済み cursor・instruction・実正 next return について、返る goal は既存実 History の一辺として到達可能。
15. `follow_history`（補助・健全性）: 任意 root と到達済み cursor・有限 instruction list・実 follow return について、最終 goal も同じ root の実 History 内にある。

以上は B4 の局所 source 橋。主型性や B4 全体の完成ではない。fresh independent invocation と selected path の限定は実装上の断片であり、仕様上の拒否規則ではないと docstring / 設計 / README に明記した。

## Verification

検証済み local source commit: `738824d2e`。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleFreshCaptureSources` — exit 0。全文:

```text
✔ [307/307] Built Yulang.CommonRoleFreshCaptureSources (1.1s)
Build completed successfully (307 jobs).
```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/yulang67-audit.lean` — exit 0。15定理の公理監査と14実行回帰。全文:

```text
'Yulang.CommonRoleFreshCaptureSources.old_below' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.fresh_ne_old' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.fresh_identity' depends on axioms: [propext]
'Yulang.CommonRoleFreshCaptureSources.extend_old' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.extend_fresh' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.extend_shared' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.generated_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.generated_fresh' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.history_owners' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.generated_requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.next_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.follow_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFreshCaptureSources.next_history' depends on axioms: [propext]
'Yulang.CommonRoleFreshCaptureSources.follow_history' depends on axioms: [propext]
```

許容された propext / Classical.choice / Quot.sound のみ。fresh map、runner、path は計算可能で、意味的型を選ぶ操作は実行器にない。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。全文:

```text
verify-lean: . @ 738824d2e (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` と staged diff check — exit 0。

focused build と個別監査は120秒上限の background process と親 shell wait で実行。初期実装では substitution 後の identifier 名と conditional の simplification に elaboration error があり、proof だけ直した。型や前提は弱めていない。最終版の recursive exactness は初回 focused check で通った。

**ローカル全体 lake build、全 Audit、広域 AxiomGate、全 verify は実行していない。** 上記 verify は diff checks only。exact source の GitHub CI は後述。

### Reproducible executable regressions

15本の公理表示の後に、次の14例を同じファイルで検証した。

```lean
import Yulang.CommonRoleFreshCaptureSources
open Yulang Yulang.CommonRoleFreshCaptureSources
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleStablePaterson (Declaration)
open Yulang.CommonRoleIntervalPaterson (Goal)

def rootDecl : Declaration := ⟨1, 0, [.pair (.var 0) (.tick (.var 1))],
  [(2, [.pair (.var 1) (.var 0)]), (3, [.var 0])]⟩
def childDecl : Declaration := ⟨2, 1, [.pair (.var 41) (.var 42)],
  [(3, [.var 41]), (3, [.var 42])]⟩
def leafDecl : Declaration := ⟨3, 2, [.var 99], []⟩
def rootGoal : Goal := ⟨1, [(.pair (.var 7) (.tick (.var 9)),
  .pair (.var 7) (.tick (.var 10)))]⟩
def firstStep : Instruction := ⟨rootDecl, 0⟩
def secondStep (position : Nat) : Instruction := ⟨childDecl, position⟩
def observation (position : Nat) : Option (List Nat × List Nat) := do
  let cursor ← follow id ⟨rootGoal, []⟩ [firstStep, secondStep position]
  let answer ← run id cursor.requests leafDecl cursor.goal
  let payload ← answer
  pure (payload.state.requests.map Prod.fst,
    CommonRoleRecursiveSourceAllocation.payloadTable payload)

example : observation 0 = some ([0, 1, 43, 44, 144], [9, 10]) := rfl
example : observation 1 = some ([0, 1, 43, 44, 144], [7, 7]) := rfl
example : observation 2 = none := rfl
-- An actual old demand, with deliberately high identity, is retained.
def old : List (CommonRoleSourceIntervalBatches.Demand Nat) := [(500, (.var 2, .var 3))]
example : boundary old = 501 := rfl
example : freshSource old 0 = 501 := rfl
example : freshSource old 99 = 600 := rfl
example : ((run id old rootDecl rootGoal).bind id).map
    (fun result => result.state.requests.map Prod.fst) = some [500, 501, 502] := rfl
example : ((run id old rootDecl rootGoal).bind id).map
    (fun result => result.state.requests.head?) = some (some (500, (.var 2, .var 3))) := rfl
-- Original candidate outcomes remain distinct.
example : (run id old rootDecl {rootGoal with role := 99}).map Option.isSome = some false := rfl
example : run id old {rootDecl with requirements := [(3, [.var 999])]} rootGoal = none := rfl
-- Repeated textual binder labels across actual calls receive fresh demand names.
def leafGoal : Goal := ⟨3, [(.var 9, .var 10)]⟩
example : ((run id [] leafDecl leafGoal).bind id).map
    (fun result => result.state.requests.map Prod.fst) = some [99] := rfl
example : (do
    let answer ← run id [] leafDecl leafGoal
    let result ← answer
    let nextAnswer ← run id result.state.requests leafDecl leafGoal
    let nextResult ← nextAnswer
    pure (nextResult.state.requests.map Prod.fst)) = some [99, 199] := rfl
-- The direct algebraic allocator preserves repeated binders within a call.
example : freshSource old 17 = freshSource old 17 := rfl
example : freshSource old 17 ≠ freshSource old 18 := by decide
```

## Publication and recovery

開始時に integration/m1-final を GitHub と git で取得し、standing orders と inbox を再読。I-4 ACTIVE、上限なし、I-11 の25分上限を確認した。integration/live work の先頭は `abefdd27c0103dea22c91529dd93ab6b6f594a9c`。cycle66 は completed かつ対応報告あり、既存作業場 clean。復旧不要。

開始心拍 `6ae8bc812c29bc92dbc6e895d60ed680ac5130ab` を公開し、exact SHA を fetch/merge。work の tracking ref は古いため、GitHub live ref と exact SHA を使った。integration は local の祖先。作業場は一つ、既存 cache を再利用し、新しい worktree や cache copy は作っていない。

source は6成果パスと running 心拍の計7パス。全 blob SHA を local git hash と照合し、最新 remote tree に重ねた SHA-only tree を作成。non-force / expected-head の一回の ref 更新で公開。書込の拒否・承認待ち・結果不明はない。

公開 source commit: `a975fed0cfbf0d40869ebf290f47da020c855dbb`。
source tree: `188d8f604e66eecf29ad1e85d5e431ea99ea1fc1`。

公開後に live ref と recursive tree を取得し、全7変更 path の mode/SHA 一致、対象外2164 blob の保持、全2171 blob、truncation なしを確認した。exact source を local に fetch/merge し、6成果 path の差分が空であることを確認した。他の branch への書込はない。

本報告と completed 心拍を続けて公開し、最終 tree を照合する。cycle 全体の変更は8パス。最終 SHA と照合結果は親へ返す。

## Yulang2 comparison

実装前に work/dots-audit を取得し、x-oracle の X13〜X16、C3-PARENT / C3-PARENT-NEG を読んだ。spec 6.3 の変数、associated equality、兄弟更新と安定後最終化を確認した。実機例は今回の一般 namespace 定理の証明ではない。新しい Yulang2 実行はしていない。

今回の fresh utility を、既存 invocation の再生成・共有・関連型 feedback の意味論に採用したとは主張しない。新たな言語意味論の選択と質問ノートはない。

## Remaining B4 bridges

主要橋は**5本のまま**: `source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

今回閉じたのは第1〜2橋の「新しい独立 local capture の計算済み demand 名前空間、任意有限の実 path に沿った合成、独立元モデルとの iff」という部分。一般の persistent source registry や有限 goal 領域は閉じていない。

次の候補:
1. `registered_capture_reuse_exact`: 明示した invocation key の初回割当と再訪時 map 再利用を実 registry に接続し、意図しない fresh 化・衝突なしを証明する。
2. `associated_feedback_graph_adequate`: ordinary 更新から graph の意味的十分性、関連型子の feedback と親再生成を共有モデルへ接続する。
3. `saturate_terminates_and_closes`: 実 driver を計算された有限 goal 領域と Paterson/K2 の停止・意味的閉包へ接続する。

## Time and limits

予定開始 2026-11-10T04:27:19Z、締切04:52:19Z。最初の環境 date は04:27:38Z。開始心拍updatedは04:29:23Z。source心拍updatedは04:35:21Z（約8.0分）で10分区切りより前に公開した。

開始時と source 公開後の空きは48G（全63G、使用13G）。使用量枠は不明。I-11 の部分目標が閉じたため、時間を埋めるだけの補題は追加しない。

## Exact source CI

source `a975fed0cfbf0d40869ebf290f47da020c855dbb`:
- core: https://github.com/momota1029/yulang/actions/runs/42756873622
- proof: https://github.com/momota1029/yulang/actions/runs/42756873772

2026-11-10T04:36:02Z 時点で両方 in_progress。最終確認を追記する。

2026-11-10T04:37:30Z に exact source の core / proof がともに completed / success と確認した。同時に10分心拍 `49587c63bf53ff2dad1c03d4dff0599cad276adc` を公開した。その後の変更は報告と心拍のみで、Lean source は変えていない。ローカル全体検証を行ったという意味ではない。

報告と completed 心拍の準備: 2026-11-10T04:38:15Z、予定開始から約10.9分。公開・最終 tree 照合を含めて終了する。

報告追記の初回 shell command は quoting error で失敗した。source の変更はなく、quoted heredoc で追記をやり直し、報告・完了心拍の local git hash と公開 blob SHA の一致を確認した。誤った途中版は branch に公開していない。
