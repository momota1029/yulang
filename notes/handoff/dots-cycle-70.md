# dots cycle 70 — boundary-input ledger and unpublished-proof verification

## Result

**I-13の第一巡をローカルで作成。I-13全体は部分達成。公開は引き続き未完了。**

cycle69の未公開証明を重複させず、最新integrationのI-13に従って、caller入力の
名前・型・依存定理・実ソースからの導出案・仕様の条番号を台帳にした。
cycle62〜69の8モジュールを中心に、source graph、関連型annotation、Main境界、
旧worklist/path/global-choice、graph compiler、条件付きouter resolverを照合した。
台帳に参照するモジュールは52個で、すべて実在を確認した。
全関連importを網羅したという主張はしない。I-13を完了するには追加の依存照合が必要。

- 台帳: `notes/design/2026-11-10-boundary-inputs-ledger.md`。
- 質問2件: 再訪時の局所binder共有、関連型糖衣と宣言検査の数え方。
- 新規Leanモジュール/定理: 0。cycle69の16定理を変更せず保持した。
- docs source commit: `ed2b60284`。integrationのlocal merge: `2c0d21d88`。
- 部分目標「現在の入力境界を具体的な回帰と仕様根拠で切り分ける」は第一巡の範囲で完了。
  B4の主要橋の完成は0本。一般resolve_exact、X13〜X16の外側入口、M1三つ組は未達。

## Useful findings

1. 非線形headの同名変数共有はspec6.2が既に根拠を持つ。Nodup headしか扱わない
   scannerのoutsideを言語拒否と読まない。実回帰でPaterson check=true、
   raw captureは重複bindingを返し、candidate inspectだけoutsideとなった。
2. 普通のwhere-only変数はspec6.3の出現回数条件で既に排除される。実check=false。
   関連型糖衣の生成binderと名前つき引数の数え方は別に質問した。
3. 実childrenが空の親の「999番目の子」を名乗るaddressed visitでもcaptureは成功する。
   有限traceの共有モデルiffは、traceの実生成・到達可能性・網羅性を証明していない。
4. 補助compileへ空tableを渡すと異なるinvocationが0へ衝突するが、public followは
   全visitsからtableを計算し、identity定理もmember前提を持つので矛盾はない。
5. 手作りregistryでは旧/新需要名が衝突し得る。exactnessの入口start oldは境界を
   構成して回避する。任意state補助とpublic入口を区別する必要がある。
6. 旧Routeは同じparent/candidate/child tripleの重複where位置を区別せず、
   cycle69 Addressは元where位置を区別する。二つを同じidentityとする橋は無い。
7. ordinary compiler graphとrole RegularGraphは異なる型。モデルexactnessと
   source graph adequacyを、同じgraphという名前だけで接続しない。

これらは既存定理の反例ではなく、caller入力として残る範囲の検証。
新しい言語意味論は決めず、質問ノートは遅延案を先頭にした。
既存cycle23/24の候補guard問題と回答済みの辞書同値問題は再質問していない。

## Recovery and current remote

開始時のlocal HEAD `38571042443582d1d06c77b0f3fa7aa558599dca`とclean statusを確認。
cycle69報告/heartbeatと8未公開pathが残っていた。remoteはcycle68 completed。
cycle69の消失/crashではなく、公開拒否でlocalに残る状態と区別し、crash報告を増やしていない。

GitHub pluginでstanding-orders/inboxを再取得・再読し、gitでも
`git fetch origin integration/m1-final work/dots-main`を実行した。
最新integration `434d3ceefce3bc2dbd8d5cb5d84c6295a9c40cf8`の追加はI-13のみ。
`git merge --no-edit origin/integration/m1-final`は成功し、inboxとcycle69を両方保持。
ACTIVE、I-11の25分上限、I-13のcycle72までの台帳要求を確認した。

開始時と06:10 UTCのread-only `git ls-remote`:

```text
434d3ceefce3bc2dbd8d5cb5d84c6295a9c40cf8 refs/heads/integration/m1-final
872066861d13cfa1784bffdaa7bfbb973998c00f refs/heads/work/dots-main
```

## Verification

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleAddressedCaptureModels`
   exit 0。最新integration取り込み後、cycle69 focused buildを確認。全文:

```text
Build completed successfully (309 jobs).

```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang70/boundary-check.lean`
   exit 0。14回帰と3入口の公理監査。全文:

```text
'Yulang.CommonRoleAddressedCaptureModels.follow_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRegisteredCaptureSources.follow_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.history_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

許容されたpropext / Classical.choice / Quot.soundのみ。
最初の検査用ファイルはnamespace略記と予約語を識別子に使ったためexit 1。
検査用ファイルだけ直し、同じ14主張を再実行してexit 0。
その後/tmpの検査ファイルとログが読めなくなったため、workspace cacheに同じ検査を
再作成し、短いfocused build/14回帰/監査を再実行して上のログを保存した。
原因不明の/tmp消失を成功した保存と扱わず、報告内にも全文を残す。
両コマンドは120秒上限、background開始、親shell wait、ログ保存で実行した。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` exit 0。全文:

```text
verify-lean: . @ ed2b60284 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

```

4. `git diff --check` / `git diff --cached --check` exit 0。
   台帳・質問2件のMarkdown相対リンクはすべて参照先あり。

**全体lake build、全Audit、広域公理gate、全verify、exact-source remote CIは未実行。**
リポジトリのLeanソース変更なし。Yulang2新規実行、質問例のparser受理確認も未実行。

### Reproducible boundary checks

```lean
import Yulang.CommonRoleAddressedCaptureModels
open Yulang
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleStablePaterson (Declaration)
open Yulang.CommonRoleIntervalPaterson (Goal)
namespace Cycle70BoundaryCheck
-- Repeated binders: raw capture and the candidate scanner have different domains.
def nonlinear : Declaration := ⟨1, 7, [.pair (.var 0) (.var 0)], []⟩
def nonlinearGoal : Goal := ⟨1, [(.pair .int .int, .pair .int .int)]⟩
example : CommonRoleStablePaterson.check nonlinear = true := rfl
example : CommonRoleIntervalCapture.supported nonlinear = false := rfl
example : CommonRoleIntervalCapture.captureArguments nonlinear.head nonlinearGoal.arguments =
    some [(0, (.int, .int)), (0, (.int, .int))] := rfl
example : CommonRoleIntervalCandidates.inspect nonlinear nonlinearGoal = none := rfl
-- An ordinary free where variable already violates the occurrence condition.
def freeWhere : Declaration := ⟨1, 8, [.tick (.var 0)], [(2, [.var 1])]⟩
def freeGoal : Goal := ⟨1, [(.tick .int, .tick .int)]⟩
example : CommonRoleStablePaterson.check freeWhere = false := rfl
example : CommonRoleIntervalCandidates.inspect freeWhere freeGoal = none := rfl
-- Address fields do not themselves certify a generated path.
def leaf : Declaration := ⟨1, 9, [.var 0], []⟩
def root : CommonRoleAddressedCaptureModels.Invocation := ⟨⟨4, []⟩, leaf⟩
def impossibleChild : CommonRoleAddressedCaptureModels.Invocation :=
    ⟨CommonRoleAddressedCaptureModels.childAddress root 999, leaf⟩
def g : Goal := ⟨1, [(.int, .int)]⟩
def v : CommonRoleAddressedCaptureModels.Visit := ⟨root, g⟩
def impossible : CommonRoleAddressedCaptureModels.Visit := ⟨impossibleChild, g⟩
example : CommonRoleAddressedCaptureModels.children root (fun _ => (.int, .int)) = [] := rfl
example : (CommonRoleAddressedCaptureModels.follow (α := Nat) id [] [impossible]).isSome = true := rfl
-- The safe public follow computes its table. An arbitrary helper table need not be complete.
example : (CommonRoleAddressedCaptureModels.compile [] v).invocation =
    (CommonRoleAddressedCaptureModels.compile [] impossible).invocation := rfl
example : v.invocation ≠ impossible.invocation := by decide
example : (CommonRoleAddressedCaptureModels.compile
    (CommonRoleAddressedCaptureModels.table [v, impossible]) v).invocation = 0 := rfl
example : (CommonRoleAddressedCaptureModels.compile
    (CommonRoleAddressedCaptureModels.table [v, impossible]) impossible).invocation = 1 := rfl
-- A caller can construct an unchecked registry. start is used by the public exactness theorem.
def old : List (CommonRoleSourceIntervalBatches.Demand Nat) := [(0, (.var 0, .var 0))]
def unchecked : CommonRoleRegisteredCaptureSources.State Nat := ⟨0, [], old⟩
example : (CommonRoleRegisteredCaptureSources.generated id unchecked 0 leaf g
    [(0, (.int, .int))]).registry.requests.map Prod.fst = [0, 0] := rfl
example : (CommonRoleRegisteredCaptureSources.generated id
    (CommonRoleRegisteredCaptureSources.start old) 0 leaf g
    [(0, (.int, .int))]).registry.requests.map Prod.fst = [0, 1] := rfl
#print axioms CommonRoleAddressedCaptureModels.follow_models_exact
#print axioms CommonRoleRegisteredCaptureSources.follow_models_exact
#print axioms CommonRoleRecursiveSourceAllocation.history_allocation
end Cycle70BoundaryCheck

```

## Publication blocker

cycle69でGitHub create_commitが、parentがintegration headでもあることを理由に二回拒否された。
今回、新しい許可は無い。**remote Git blob/tree/commit/ref書込は一度も試行していない。**
push、ファイル分割、同等の別経路で回避していない。read/fetchとlocal commitだけを行った。
公開済み成果ファイル数は0。開始/10分心拍もremoteへ公開していない。
local heartbeatは記録として更新したが、remoteから観測できる心拍の代わりにはならない。

必要な新承認の対象は、work/dots-main公開のためのGit object作成/ref更新。
integrationその他のref更新は行わない。許可後、最新integrationとlive workを読み直し、
対象外pathを保持した一括non-force/expected-head公開と全blob照合を行う。
それまで同じ拒否操作を再試行しない。

最新integrationとの差分、cycle69と合計12未公開path:
- `lean/Yulang/CommonRoleAddressedCaptureModels.lean`
- `lean/Yulang.lean`
- `lean/Audit.lean`
- `lean/README.md`
- `notes/design/2026-11-10-cycle69-addressed-capture-models.md`
- `notes/design/2026-11-10-boundary-inputs-ledger.md`
- `notes/design/INDEX.md`
- `notes/questions/2026-11-10-cycle70-invocation-sharing-boundary.md`
- `notes/questions/2026-11-10-cycle70-associated-sugar-checking.md`
- `notes/handoff/dots-cycle-69.md`
- `notes/handoff/dots-cycle-70.md`
- `notes/heartbeat/dots-main.md`

## Remaining work

B4の主要橋は5本:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、
`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

次の候補:
1. I-13台帳をMain/Auditの関連依存と照合し、未列挙のsource-specific Protocol、
   guarded候補/CorrelatedCarrier、ordinary-state/graph変換のcaller前提を補う。
2. 実child展開とaddressed traceを結ぶ到達可能性/網羅性を独立に定義する。
   任意traceのモデルiffを全生成仕事の有限性と取り違えない。
3. annotations/receiver/outputを実宣言から導くassociated feedbackの橋を設計する。
   質問Q1/Q2の未確定事項は勝手に決めず分離する。

## Time and resources

予定開始2026-11-10T05:57:00Z、最初のdate記録05:59:01Z。
報告作成 2026-11-10T06:15:33Z、予定開始から18.6分。
I-11の25分上限内。時間を埋めるための補題は追加していない。
開始時/終了前とも空き48G（全63G、使用13G）。作業場/cacheは一つを再利用。
新worktree/cacheコピーなし。使用量枠は不明。
