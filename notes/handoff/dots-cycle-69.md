# dots cycle 69 — structural addressed capture models

## Summary

**証明の部分目標は閉じた。公開はブロックされ、未完了。**

元の root occurrence と親宣言/where-list位置から構造的 invocation を作り、任意有限 trace から numeric key を計算する橋を追加した。同じ端点や同じ binder 綴りだけでは同一視しない。完全な宣言を保持するので、異なる宣言が同じ numeric label を持っていても誤って共有しない。実 registered capture の where children 全体を、元の位置を保ったアドレスつきで返す。二つの兄弟が同じ goal でも区別され、端点が変わって再生成されても同じ where 位置のアドレスを保つ。

`follow_models_exact` は、任意有限の addressed trace の実成功かつ最終モデルの存在 iff 初期モデルと、全ての元 head/where を同時に満たす一つの構造的 invocation/binder valuation の存在、を証明する。registry や generated atoms を参照しない独立 `Fits` との iff。モデルの整合性、実成功、source map を前提に置かない。

さらに、visit を追加しても既存 index が変わらず、`follow_append` は既に計算した prefix を replay/renumber せず続行できることを証明する。同じ addressed visits の並替えと、変更のない有限 pass の二重実行は、モデルの存在を変えない。端点が絞られた異なる visit の制約は消していない。

**境界:** root 番号と有限 visit 列は入力のまま。ソース構文からの root elaboration、全 visit の到達可能性/網羅性、全生成 goal の有限性、associated feedback、graph adequacy、飽和、四方向分類、辞書の同値、外側 resolve_exact、X13〜X16 の外側入口、M1三つ組は未完。既にaddressを持つvisitの並替えと、ソース宣言のwhere位置そのものを書き換えることは別であり、後者は今回の定理に含まない。実装断片の限定で、仕様上の新しい拒否規則ではない。

## Theorems and quantified claims

新規 `lean/Yulang/CommonRoleAddressedCaptureModels.lean`、16公開定理。全て Audit に追加し、Yulang から import した。

1. `children_goals`（補助・健全性/完全性）: 任意親 invocation と任意 endpoint substitution に対し、アドレスつき children の goal 列は実 expand の全 goal 列に等しい。
2. `child_address_exact`（補助・健全性/完全性）: 任意二親 invocation・任意二位置に対し、子アドレスが等しい iff 親 invocation と位置が両方等しい。
3. `children_addresses`（補助・健全性/完全性）: 任意親 invocation と任意 substitution に対し、生成したアドレス列は元 requirements の全位置列を写したものに等しい。重複goalを落とさない。
4. `children_regenerate`（補助）: 任意親と任意二 substitution に対し、子のアドレス列は等しい。端点に依存しない。
5. `children_at`（補助・健全性/完全性）: 任意親・substitution・有効な元 requirement index に対し、その位置の実 children は計算アドレスと元 requirement をinstantiateしたgoalの対に厳密に等しい。
6. `index_exact`（補助・健全性/完全性）: 任意有限 table とその任意二 member に対し、first-position index が等しい iff invocation が等しい。
7. `compile_append`（補助）: 任意 earlier/later trace と earlier の任意 visit に対し、laterを足したtableでcompileしても元compile結果と等しい。
8. `compile_bounded`（補助）: 任意traceの任意memberに対し、計算invocation indexはtrace長未満。上限をcallerから受けない。
9. `compiled_identity`（局所健全性/完全性）: 任意traceの任意二visitに対し、実compileのnumeric invocationが等しい iff 構造的invocationが等しい。
10. `step_no_new_failure`（局所健全性/完全性）: 任意slots/table/registry/visitに対し、実stepから追加provenanceを除くと元registered runnerの三方向結果に厳密に戻る。新しい失敗なし。
11. `step_children`（局所健全性）: 任意実step成功結果に対し、返るtagged childrenは実capture bindingsで生成した全childrenに等しい。
12. `follow_append`（局所健全性/完全性・補助）: 任意slots/初期demands/earlier/laterに対し、連結traceの一括実行は、earlierの結果を引き継ぎlaterを実行する結果と等しい。成功やモデルの前提なし。
13. `shared_models_exact`（局所健全性/完全性）: 任意slots/assignment/有限traceに対し、計算numeric registry用の共有model iff 構造的invocation/binderの独立共有model。両方向のvaluationを構成する。
14. `follow_models_exact`（局所健全性/完全性）: 任意slots/assignment/初期demands/有限traceに対し、モデルを持つ実最終成功stateが存在 iff 初期demandsのmodelと、全元head/whereを満たす一つの構造的共有valuationが存在。
15. `reorder_models`（局所健全性/完全性・補助）: 任意slots/assignment/初期demandsと、同じaddressed visitsを並替えた任意二traceに対し、モデルを持つ実成功の存在は同値。出力atom列や辞書の同一性は主張しない。
16. `repeat_models`（局所健全性/完全性・補助）: 任意slots/assignment/初期demands/traceに対し、同一traceを二度連結したモデルつき成功の存在 iff 一度の存在。端点refinementを同一視しない。

主型性、全言語健全性/完全性、B4完成は主張していない。

## Verification

Source local commit: `94cf57484`。6成果path。既存のLeanコードは変更せず、許可された接続ファイルに追記した。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleAddressedCaptureModels` — exit 0。全文:

```text
✔ [309/309] Built Yulang.CommonRoleAddressedCaptureModels (1.2s)
Build completed successfully (309 jobs).
```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/yulang69-audit.lean` — exit 0。16公開定理の公理監査と18実行回帰。全文:

```text
'Yulang.CommonRoleAddressedCaptureModels.children_goals' depends on axioms: [propext]
'Yulang.CommonRoleAddressedCaptureModels.child_address_exact' depends on axioms: [propext]
'Yulang.CommonRoleAddressedCaptureModels.children_addresses' depends on axioms: [propext]
'Yulang.CommonRoleAddressedCaptureModels.children_regenerate' depends on axioms: [propext]
'Yulang.CommonRoleAddressedCaptureModels.children_at' depends on axioms: [propext]
'Yulang.CommonRoleAddressedCaptureModels.index_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.compile_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.compile_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.compiled_identity' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.step_no_new_failure' depends on axioms: [propext]
'Yulang.CommonRoleAddressedCaptureModels.step_children' depends on axioms: [propext]
'Yulang.CommonRoleAddressedCaptureModels.follow_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.shared_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.follow_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.reorder_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAddressedCaptureModels.repeat_models' depends on axioms: [propext, Classical.choice, Quot.sound]
```

許容された propext / Classical.choice / Quot.sound のみ。初回のnamespace記法、map/zipIdx、存在量化の再配置、名前の衝突に関するelaboration errorを修正し、最終ビルドは警告なし。定理の主張や前提は弱めていない。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。全文:

```text
verify-lean: . @ 94cf57484 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` と `git diff --cached --check` — exit 0。

ビルド/個別監査は120秒上限を付けたbackground process、ログ保存、親shellでwaitした。**ローカル全体lake build、全Audit、広域公理gate、全verifyは実行していない。exact source CIも未実行。** 公開ブロックのため、新sourceに対するremote tree照合やCI成功の主張はできない。

### Reproducible regressions

```lean
import Yulang.CommonRoleAddressedCaptureModels
open Yulang Yulang.CommonRoleAddressedCaptureModels
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleStablePaterson (Declaration)
open Yulang.CommonRoleIntervalPaterson (Goal)
def rootDecl : Declaration := ⟨1, 0, [.pair (.var 0) (.tick (.var 1))],
  [(3, [.var 0]), (3, [.var 0])]⟩
def leafDecl : Declaration := ⟨3, 2, [.var 99], []⟩
def rootInvocation : Invocation := ⟨⟨7, []⟩, rootDecl⟩
def rootGoal : Goal := ⟨1, [(.pair (.var 7) (.tick (.var 9)),
  .pair (.var 7) (.tick (.var 10)))]⟩
def changedRoot : Goal := ⟨1, [(.pair (.var 20) (.tick (.var 21)),
  .pair (.var 22) (.tick (.var 23)))]⟩
def leafGoal : Goal := ⟨3, [(.var 7, .var 7)]⟩
def v0 : Visit := ⟨rootInvocation,rootGoal⟩
def v1 : Visit := ⟨⟨childAddress rootInvocation 0,leafDecl⟩,leafGoal⟩
def v2 : Visit := ⟨⟨childAddress rootInvocation 1,leafDecl⟩,leafGoal⟩
def v3 : Visit := ⟨rootInvocation,changedRoot⟩
def visits := [v0,v1,v2,v3]
def old : List (CommonRoleSourceIntervalBatches.Demand Nat) := [(500, (.var 2,.var 3))]
def final := follow id old visits
example : (visits.map (compile (table visits))).map CommonRoleRegisteredCaptureSources.Visit.invocation = [0,1,2,0] := rfl
example : final.map (fun state => state.requests.map Prod.fst) =
  some [500,501,502,503,504,501,502] := rfl
example : final.map (fun state => state.table) = some [(0,0),(0,1),(1,99),(2,99)] := rfl
example : final.map (fun state => state.boundary) = some 501 := rfl
example : v1.goal = v2.goal := rfl
example : v1.invocation ≠ v2.invocation := by decide
example : childAddress rootInvocation 0 ≠ childAddress rootInvocation 1 := by decide
example : (compile (table [v0,v1]) v0).invocation = (compile (table visits) v0).invocation := rfl
example : (compile (table [v0,v1]) v1).invocation = (compile (table visits) v1).invocation := rfl
example : (compile (table visits) v0).invocation = (compile (table visits) v3).invocation := rfl
example : (compile (table [v0,⟨{rootInvocation with address.root := 8},rootGoal⟩])
  ⟨{rootInvocation with address.root := 8},rootGoal⟩).invocation = 1 := rfl
example : (compile (table [v0,⟨{rootInvocation with declaration.key := 9},rootGoal⟩])
  ⟨{rootInvocation with declaration.key := 9},rootGoal⟩).invocation = 1 := rfl
example : ((step id (table visits) (CommonRoleRegisteredCaptureSources.start old) v0).bind id).map
  (fun result => result.2.map Prod.fst) = some [childAddress rootInvocation 0,childAddress rootInvocation 1] := rfl
example : ((step id (table visits) (CommonRoleRegisteredCaptureSources.start old) v0).bind id).map
  (fun result => result.2.map Prod.snd) = some [leafGoal,leafGoal] := rfl
example : follow id old [⟨rootInvocation,{rootGoal with role := 99}⟩] = none := rfl
example : follow id old ([] : List Visit) = some (CommonRoleRegisteredCaptureSources.start old) := rfl
example : (step id (table visits) (CommonRoleRegisteredCaptureSources.start old)
  ⟨rootInvocation,{rootGoal with role := 99}⟩).map Option.isSome = some false := rfl
example : (step id (table visits) (CommonRoleRegisteredCaptureSources.start old)
  ⟨{rootInvocation with declaration.requirements := [(3,[.var 999])]},rootGoal⟩) = none := rfl
```

## Publication blocker and recovery

開始時に `integration/m1-final` をGitHubとgitで取得し、standing orders/inboxを再読した。ACTIVE、最大サイクル上限なし、I-11の25分上限を確認。live integrationとworkの両方が `872066861d13cfa1784bffdaa7bfbb973998c00f` を指していた。cycle68はcompleted、報告あり。既存cloneはclean、作業場とcacheを一つだけ再利用。復旧不要。tracking refのworkは古いため、live GitHub refとexact SHAを根拠にした。

開始心拍用blob `66c57a97183b8d829489e24dfeecc696bbd70313` と、その一pathだけを重ねたtree `9f5335b58d5383692078cd8fe6b78ca6004c0900` は作成された。しかし `create_commit` が、親SHAがintegration headでもあることを理由に範囲外と判定され拒否された。work自身も同じSHAを指すことをlive refで再取得し、既知未実行の操作を一回だけ再試行したが、同じ理由で再び拒否された。**remote commit/ref更新は一度も成功していない。** 別経路で回避していない。

05:36:56 UTCにもwork live refが元の `872066861...` であることを確認した。開始心拍も10分心拍も公開できていない。ローカルのheartbeat/reportだけを保存する。今回の公開済み成果ファイル数は **0**。blob/treeはブランチ未到達の準備物であり、公開完了に数えない。

解除に必要な確認の対象は、work/dots-mainの更新に必要なGit blob/tree/commitオブジェクトの作成を、親SHAがintegrationと同じ場合でも許可すること。integrationその他のref更新は行わない。新しい承認なしで同じ操作を再試行しない。

次回は新しい証明を重複させる前に、このlocal source commitと6成果path、cycle69報告/心拍を確認する。承認が得られたら最新remote treeに変更pathだけを重ね、non-force/expected-headでworkだけを更新し、全変更blobと対象外pathの保持を照合する。最新integrationの変更があれば優先して取り込む。

未公開path:
- lean/Yulang/CommonRoleAddressedCaptureModels.lean
- lean/Yulang.lean
- lean/Audit.lean
- lean/README.md
- notes/design/2026-11-10-cycle69-addressed-capture-models.md
- notes/design/INDEX.md
- notes/handoff/dots-cycle-69.md
- notes/heartbeat/dots-main.md

## Yulang2 comparison

変更前にwork/dots-auditを取得し、x-oracleのX13〜X16とC3-PARENT/C3-PARENT-NEGを参照した。spec 6.3のsource共有、関連型等式、兄弟の再計算と安定後の最終化を確認した。これらは今回の有限tableアルゴリズムやsource identityの一般証明そのものではない。新しいYulang2実行なし。

root番号は明示入力、childは元where位置、候補は完全な元宣言、という既存の構造的実装境界を明示した。観察同値でsourceを統合せず、新しい言語仕様や辞書観察同値は決めていない。質問ノート追加なし。

## Remaining B4 bridges

主要橋は **5本のまま**: `source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

今回閉じた第1〜2橋の部分: 構造的where provenanceから計算した有限invocation identity、実capture出力のアドレス保持、prefix再開、全元head/where共有モデルiff。次の候補:
1. `associated_feedback_graph_adequate`: ordinary更新と関連型等式を同じ構造的keyに接続し、実graph adequacyを閉じる。
2. `generated_work_closed`: caller入力の有限visit列を、rootと実child展開から計算された全仕事領域に置き換える。
3. `saturate_terminates_and_closes`: 上記領域と実driver、Paterson/K2を接続し、再生成の停止・閉包を証明する。

## Time and limits

予定開始2026-11-10T05:27:19Z、締切05:52:19Z。最初のdateは05:28:37Z。報告準備 2026-11-10T05:38:45Z、予定開始から11.4分。部分目標は閉じ、公開の許可待ちが残った。時間を埋めるための定理は追加しない。

開始時/終了時とも空き48G、全63G、使用13G。新worktree/cache copyなし。使用量枠は不明。
