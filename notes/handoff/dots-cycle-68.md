# dots cycle 68 — persistent keyed capture registry

## Summary and scope

**部分目標は閉じた。** 明示した invocation key と local binder の対を有限 registry に登録し、実 candidate capture へ接続した。同じ invocation/binder の再訪では元の demand 名を保持し、別 invocation の同じ binder 綴りは別名になる。goal の endpoint が絞り込まれても、同じ宣言の accepted capture は同じ binder 列を返す。全キーが既登録の再訪では registry 自体も増えない。途中に任意有限の別 capture を挟んでも、既存の割当名は変わらない。

さらに、単発の registry 補題だけで終わらず、**任意有限の実 visit 列と独立した元共有モデルとの iff** を閉じた。`follow_models_exact` は、実 runner がモデルを持つ最終 request history を返す iff 初期 demand にモデルがあり、一つの invocation/binder valuation が全 visit の元 head と where template を満たす、と証明する。`VisitsFit` は実行器・registry・割当済み自然数名・ordinary atom を参照しない。成功や整合性や共通 valuation を前提に置かず、旧 valuation と共有 keyed valuation から flat valuation を構成する。

cycle67 の fresh-only utility との違いは、再訪を独立した local existential に分離しないこと。同じキーの2つの区間を再訪すると、old/new の両方向の制約が実際に追加される。同じ binder 綴りでも別 invocation の場合には、その交差制約は追加されない。両方を実行回帰で確認した。

**境界を維持:** invocation key と有限 visit 列は caller が渡す。source occurrence、candidate identity、親義務の経路から key を導くところは未接続。新しい言語意味論として何を同一 invocation とみなすか決めていない。実 caller の全生成 goal の有限性、associated equality の feedback、飽和停止・意味的閉包・最終分類・辞書順・外側 resolve_exact・X13〜X16 の外側入口・M1 三つ組は未完。実装断片の限定であり、仕様上の拒否範囲を追加したものではない。既存 structural linear interval grammar を広げていない。

## Theorems and quantified claims

新規 `lean/Yulang/CommonRoleRegisteredCaptureSources.lean` の21公開定理を Audit に登録し、Yulang から import。既存 Lean の変更は許可された接続ファイルへの追記のみ。

1. `register_old`（補助・健全性）: 任意 table・key batch・既存 member について、登録後も member。
2. `register_new`（補助・完全性）: 任意 table・key batch と batch 内の任意 key について、登録後にその key が存在する。
3. `source_preserved`（補助・健全性）: 任意 boundary・table・追加 batch・既存 key について、登録後の割当名は以前と等しい。
4. `source_identity`（局所健全性・完全性）: 任意 boundary・table とそこに存在する任意二 key について、割当名が等しい iff key が等しい。
5. `register_idempotent`（補助）: 任意 table と batch について、同じ batch を続けて登録しても二回目は table を変えない。
6. `source_fresh`（補助・健全性）: 任意初期 demand list・table・key・初期 demand member について、計算した境界以降の割当名はその初期名と異なる。
7. `capture_keys`（補助・健全性）: 任意 structural Capture derivation について、返る binder 列は元 Form の変数列に厳密に等しい。
8. `capture_arguments_keys`（補助・健全性）: 任意 CaptureArguments derivation について、返る binder 列は元 argument Forms の変数列に厳密に等しい。
9. `accepted_keys`（補助・健全性）: 任意 invocation・宣言・goal・bindings と Accepts derivation について、登録する key 列は元宣言の head 変数列から計算した列に等しい。endpoint に依存しない。
10. `run_exact`（局所健全性・完全性）: 任意 slots・assignment・state・invocation・宣言・goal・result について、実正 return と ordinary model iff 独立した Accepts・実生成 result の一致・一つの valuation による旧 demand と元 head/where の共有モデル。
11. `generated_key_present`（補助・完全性）: 任意 state・invocation・binding list と任意 binding member について、実生成で使う対キーは登録済み。
12. `generated_identity`（局所健全性・完全性）: 任意 state・invocation・binding list とその任意二 member について、生成した二つの demand 名が等しい iff binder 名が等しい。
13. `generated_requests`（補助・健全性）: 任意入力について、生成後の実 request history は旧 history と実 capture demand list の連結そのもの。旧 occurrence を落とさない。
14. `recapture_registry`（補助・健全性）: 任意 state・invocation・宣言と、異なってよい二 goal・二 bindings への Accepts derivation について、最初の登録後に次の capture を登録しても table は変わらない。
15. `run_preserves_sources`（補助・健全性）: 任意実正 return について、境界と全旧 table member・割当名を保持する。model の存在や子辞書の成功は仮定しない。
16. `follow_preserves_sources`（補助・健全性）: 任意有限 visit 列・初期/最終 state と実成功 return について、境界と全旧 table member・割当名を保持する。任意の割込み capture と再訪を含む。
17. `generated_requests_exact`（局所健全性・完全性）: 任意入力・assignment について、生成 ordinary atoms のモデル iff 実 retained request history のモデル。Accepts 前提も不要。
18. `visits_fit_returns`（局所完全性）: 任意 slots・assignment・keyed valuation・有限 visit 列とその独立 VisitsFit について、任意初期 state から実成功 return が存在する。
19. `follow_shared_exact`（局所健全性・完全性、条件つき補助）: 任意実成功有限列と、最終 table の有限 key で flat/keyed valuation が一致するなら、最終 SharedFits iff 初期 SharedFits かつ全元 VisitsFit。この一致前提は最終定理で構成して外す。
20. `extend_key`（補助）: 任意境界・table・旧 valuation・keyed valuation と table member について、構成した flat valuation は割当名で指定 key の値に一致する。
21. `follow_models_exact`（局所健全性・完全性）: 任意 slots・assignment・初期 demand list・有限 visit 列について、モデルを持つ実成功最終 state が存在する iff 初期 demands のモデルが存在し、全元 head/where を同時に満たす一つの keyed valuation が存在する。source map・成功・整合性・有限長の固定上限・子辞書成功の前提なし。

主型性、全言語の健全性・完全性、B4 完成を主張していない。

## Verification

検証済み local source commit: `a55ca95b3`。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleRegisteredCaptureSources` — exit 0。全文:

```text
✔ [308/308] Built Yulang.CommonRoleRegisteredCaptureSources (1.4s)
Build completed successfully (308 jobs).
```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/yulang68-audit.lean` — exit 0。21公開定理の公理監査と18実行回帰。全文:

```text
'Yulang.CommonRoleRegisteredCaptureSources.register_old' does not depend on any axioms
'Yulang.CommonRoleRegisteredCaptureSources.register_new' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.source_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.register_idempotent' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.source_fresh' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.capture_keys' depends on axioms: [propext]
'Yulang.CommonRoleRegisteredCaptureSources.capture_arguments_keys' depends on axioms: [propext]
'Yulang.CommonRoleRegisteredCaptureSources.accepted_keys' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.generated_key_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.generated_identity' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.generated_requests' does not depend on any axioms
'Yulang.CommonRoleRegisteredCaptureSources.recapture_registry' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.run_preserves_sources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.follow_preserves_sources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.generated_requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.visits_fit_returns' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.follow_shared_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.extend_key' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.follow_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。全文:

```text
verify-lean: . @ a55ca95b3 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` と staged diff check — exit 0。公開 exact source と local HEAD の6成果 path 差分も exit 0。

許容された propext / Classical.choice / Quot.sound のみ。初期 proof の dependent index rewrite と型透明性の elaboration error を修正した。定理の型・前提は弱めていない。focused build と個別監査は120秒上限の background process、ログ保存、親 shell wait で実行。

**全体 lake build、全 Audit、広域 AxiomGate、全 verify はローカルで実行していない。** 上記 verify は diff checks only。exact source CI は後述。

### Reproducible executable regressions

```lean
import Yulang.CommonRoleRegisteredCaptureSources
open Yulang Yulang.CommonRoleRegisteredCaptureSources
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleStablePaterson (Declaration)
open Yulang.CommonRoleIntervalPaterson (Goal)

def rootDecl : Declaration := ⟨1, 0, [.pair (.var 0) (.tick (.var 1))],
  [(2, [.pair (.var 1) (.var 0)]), (3, [.var 0])]⟩
def leafDecl : Declaration := ⟨3, 2, [.var 99], []⟩
def rootGoal : Goal := ⟨1, [(.pair (.var 7) (.tick (.var 9)),
  .pair (.var 7) (.tick (.var 10)))]⟩
def changedRoot : Goal := ⟨1, [(.pair (.var 20) (.tick (.var 21)),
  .pair (.var 22) (.tick (.var 23)))]⟩
def leafGoal : Goal := ⟨3, [(.var 9, .var 10)]⟩
def old : List (CommonRoleSourceIntervalBatches.Demand Nat) := [(500, (.var 2, .var 3))]
def visits : List Visit := [⟨10, rootDecl, rootGoal⟩, ⟨11, leafDecl, leafGoal⟩,
  ⟨10, rootDecl, changedRoot⟩]
def final := follow id (start old) visits
example : final.map (fun state => state.requests.map Prod.fst) =
    some [500,501,502,503,501,502] := rfl
example : final.map State.table = some [(10,0),(10,1),(11,99)] := rfl
example : final.map State.boundary = some 501 := rfl
example : final.map (fun state => state.requests.head?) = some (some (500, (.var 2,.var 3))) := rfl
example : register [(10,0),(10,1),(11,99)] [(10,0),(10,1)] = [(10,0),(10,1),(11,99)] := rfl
example : register [] [(4,8),(4,8)] = [(4,8),(4,8)] := rfl
example : register [(4,8),(4,8)] [(4,8),(4,8)] = [(4,8),(4,8)] := rfl
example : source 501 [(10,0),(10,1),(11,99)] (10,0) = 501 := rfl
example : source 501 [(10,0),(10,1),(11,99)] (11,99) = 503 := rfl
example : (run id (start old) 10 rootDecl {rootGoal with role := 99}).map Option.isSome = some false := rfl
example : run id (start old) 10 {rootDecl with requirements := [(3,[.var 999])]} rootGoal = none := rfl
example : follow id (start old) [⟨10,rootDecl,{rootGoal with role := 99}⟩] = none := rfl
example : follow id (start old) [] = some (start old) := rfl

def flatDecl : Declaration := ⟨1, 0, [.var 5], []⟩
def firstGoal : Goal := ⟨1, [(.var 0,.var 1)]⟩
def nextGoal : Goal := ⟨1, [(.var 2,.var 3)]⟩
def twice (key : Nat) := do
  let first ← (run id (start ([] : List (CommonRoleSourceIntervalBatches.Demand Nat))) 7 flatDecl firstGoal).bind id
  let next ← (run id first.registry key flatDecl nextGoal).bind id
  pure next
example : (twice 7).map (fun result => result.registry.table) = some [(7,5)] := rfl
example : (twice 8).map (fun result => result.registry.table) = some [(7,5),(8,5)] := rfl
-- Reusing a key adds both cross-visit directions. Distinct invocation keys do not alias.
example : (twice 7).map (fun result => result.candidate.state.atoms) =
    some [.tyLe (.var 0) (.var 1), .tyLe (.var 0) (.var 3),
      .tyLe (.var 2) (.var 1), .tyLe (.var 2) (.var 3)] := rfl
example : (twice 8).map (fun result => result.candidate.state.atoms) =
    some [.tyLe (.var 0) (.var 1), .tyLe (.var 2) (.var 3)] := rfl

def closedDecl : Declaration := ⟨1,0,[.int],[]⟩
def closedGoal : Goal := ⟨1,[(.int,.int)]⟩
example : ((run id (start old) 44 closedDecl closedGoal).bind id).map
    (fun result => result.registry.table) = some [] := rfl
```

## Publication and recovery

開始時に integration/m1-final を GitHub と git で取得し、standing orders と inbox を再読。I-4 ACTIVE、上限なし、I-11 の25分上限を確認。integration と live work の開始 head は `75edb10e7240476649ea660eb2bf0beb719df9f1`。cycle67 は completed と対応報告あり。既存作業場 clean、復旧不要。

開始心拍 `0234fb7b0e56cb63a589ecf8f43d15a08e8f2953` を公開し、exact SHA を fetch/merge。integration は local の祖先。work tracking ref が古いことがあるため、GitHub live ref と exact SHA を使用。作業場一つと既存 cache を再利用、新しい worktree と cache copy は作っていない。

source は6成果 path と running 心拍の計7 path。既存の大きい Audit/README の読出しは初回出力が切れたため、文字数で小分けしてから組み立てた。全 blob SHA を local git hash と照合し、最新 remote base tree に変更7 path だけを重ねた SHA-only tree を作成。non-force / expected-head の一回の ref 更新で公開。書込拒否・承認待ち・結果不明なし。

source commit: `c410cb4a0f7c00929c84a2da729bb057805c06a2`。
source tree: `4d98991b55e4da8c308e80eedf3ec2d3049c86f5`。

公開後に live ref と recursive tree を再取得。全7変更 blob の mode/SHA 一致、対象外2167 blob の保持、全2174 blob、truncation なしを確認した。続いて進捗心拍 `14cb9805d7c22fed1837fcd50bd320f06b38eabd` を公開。exact remote source/heartbeat を local に取得・merge し、6成果 path の差分が空と確認。他 branch への書込なし。

本報告と completed 心拍を続けて公開し、最終 tree を照合する。cycle 全体では8変更 path。最終 SHA と照合結果は親に返す。

## Yulang2 comparison

実装前に work/dots-audit を取得し、x-oracle の X13〜X16 と C3-PARENT / C3-PARENT-NEG を読んだ。spec 6.3 の source 共有・関連型等式・兄弟更新と安定後の最終化を確認。旧実機例は有限registryの一般証明ではない。新しい Yulang2 実行はしていない。

何を同一 invocation とするかは caller の明示入力として残す。equal goal、equal endpoint observation、同じ binder 綴りだけで invocation を同一視しない。新しい言語意味論の選択はせず、質問ノートは追加していない。

## Remaining B4 bridges

主要橋は**5本のまま**: `source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

今回閉じた部分は第1〜2橋の「persistent explicit invocation registry、実 capture の再訪共有、任意有限列の元共有モデルとの iff」。source parser からの key 導出・associated equality feedback・有限 goal 領域は未完。

次の候補:
1. `source_invocation_key_exact`: 実 source 義務・candidate・親子位置から key を計算し、再生成時は同じ key、独立義務は異なる key と証明する。
2. `associated_feedback_graph_adequate`: 実 ordinary 更新と関連型子の feedback を、registry の同じ keyed valuation と graph adequacy に接続する。
3. `saturate_terminates_and_closes`: caller が渡す有限 visit 列を、計算された全仕事領域と実 driver に置き換え、Paterson/K2 による停止・閉包を証明する。

## Time and limits

予定開始 2026-11-10T04:57:19Z、締切05:22:19Z。最初の環境 date は04:57:09Z。開始心拍updatedは04:58:10Z。source準備心拍updatedは05:06:15Z、source ref更新完了は05:09:12Z。その間に大きい接続ファイルの読出し分割と公開が入り、10分区切り05:07:19Zより約2分遅れて公開となった。直後の05:09:25Zに進捗心拍を再公開した。今後は大きいblob準備前に心拍を先に公開する。

開始時と source 公開後の空きは48G（全63G、使用13G）。使用量枠は不明。部分目標を閉じた後に時間を埋めるためだけの補題は追加していない。

## Exact source CI

source `c410cb4a0f7c00929c84a2da729bb057805c06a2`:
- core: https://github.com/momota1029/yulang/actions/runs/42760298286
- proof: https://github.com/momota1029/yulang/actions/runs/42760298716

05:09:25Zの確認では両方 in_progress。最終確認を続けて記録する。

05:11:22Z に exact source の Core CI と Lean inference kernel がともに completed / success と確認した。その後の変更は報告と心拍のみで、Lean source は変えていない。ローカル全体検証を行ったという意味ではない。

報告と completed 心拍の準備: 2026-11-10T05:11:30Z、予定開始から約14.2分。最終公開・tree照合を含め、締切までに終了する。
