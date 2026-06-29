## 結論

**scope-local eval/request/marker lanes を実装して narrow executor に進むのが本線**だよ〜。

ただし、いきなり「速い executor」を作るより、次はこういう順がいい。

```text
1. ScopeTree + local lanes を shadow で固定
2. legacy continuation tree への materialize / replay を必ず持つ
3. narrow executor は「ProviderEnv child scope で root marker が一致した形」だけ有効化
4. それ以外は旧 tree に即 fallback
```

flat trace が失敗して、ProviderEnv を child scope にしたら root marker が合ったなら、これはかなり強い証拠だねぇ。失敗原因はたぶん「continuation を線形 trace として読むと、ProviderEnv が marker ownership / root exposure / handler hygiene の境界をまたいでしまう」こと。
だから次の構造は **flat ResumePlan** じゃなくて、**scope tree の各 node に local lane を持たせる形**が自然だと思うよ〜。

---

## 推奨ルート

### 1. `ScopePlan` を first-class にする

イメージはこれ。

```rust
struct ScopePlan {
    kind: ScopeKind,
    eval_lane: EvalLane,
    request_lane: RequestLane,
    marker_lane: MarkerLane,
    provider_children: SmallVec<[ScopePlanId; 2]>,
    exit: ScopeExit,
}

enum ScopeKind {
    Root,
    ProviderEnv {
        provider_delta: ProviderDeltaId,
        hygiene_baseline: ProviderHygieneBaseline,
    },
    Marker {
        marker_delta: MarkerDeltaId,
    },
    Catch {
        request_delta: RequestBoundaryDelta,
    },
}
```

大事なのは、`ProviderEnv` を lane の中の opcode にしないこと。
今回 child scope で root marker が一致したなら、`ProviderEnv` は「イベント」じゃなくて「局所世界を変える node」と見る方が安全だねぇ。

今の continuation は `Then`、ordinary eval frame、`CatchBody`、`MarkerFrame`、`ProviderEnv` が同じ enum に混ざっている形で、resume 時にそこを再帰的に歩く作りになっている。ここから scope/evidence を外へ出す、という方向は前の仮説とも合っているよ〜。

---

## 2. lane の責務を分ける

### `eval_lane`

ordinary frame だけ。

```text
ForceThunk
ApplyCallee
ApplyArg
AdaptValue
CaseScrutinee
TupleItems
RecordFields
SelectBase
BlockStmt
...
```

ここには `ProviderEnv`、`MarkerFrame`、`CatchBody` を入れない。

### `request_lane`

`CatchBody` / `RefSet` / routed request boundary だけ。

```rust
enum RequestLane {
    None,
    CatchSameHandler { catch_expr: ExprId, arms: Rc<[CatchArm]>, env: Env },
    CatchForeignHandler { catch_expr: ExprId, arms: Rc<[CatchArm]>, env: Env },
    CatchNoRoutedHandler { catch_expr: ExprId, arms: Rc<[CatchArm]>, env: Env },
    RefSet,
}
```

最初の executor 対象は `CatchSameHandler` か `None` だけでいい。
`CatchForeignHandler` は legacy materialize fallback に逃がすのが安全だねぇ。

### `marker_lane`

marker enter/exit の局所操作だけ。

```rust
struct MarkerLane {
    delta: MarkerDeltaId,
    root_marker_effect: RootMarkerEffect,
    active_add_id_ops: Rc<[AddIdEnterOp]>,
    handler_boundary_ops: Rc<[HandlerBoundaryEnterOp]>,
}
```

`root_marker_effect` を明示的に持つのがかなり大事。
今回「root marker が合った」が成功判定になっているなら、それを executor の暗黙性質にしない方がいい。lane の検証対象として残す。

### `provider_children`

`ProviderEnv` はここ。

```rust
struct ProviderChild {
    provider_delta: ProviderDeltaId,
    child: ScopePlanId,
}
```

ProviderEnv を flat trace の途中イベントに戻すと、また同じ失敗を踏みやすいと思うよ〜。

---

## narrow executor に進んでいい条件

進んでいい。ただし、最初の有効化条件はかなり狭く切る。

```text
- ProviderEnv child scope split で root marker が legacy と一致
- child scope は単一 entry / 単一 exit
- sibling scope をまたぐ resume がない
- Catch は None か CatchSameHandler だけ
- RefSet boundary なし
- legacy bridge なし
- resume_delta は marker_lane で完全に表現済み、または reject
- ProviderEnv miss を invisibility 証明に使わない
- any ProviderEnv を permission evidence に使わない
- fallback materialize が常に可能
```

この条件なら、narrow executor は「意味論を変える実行器」じゃなくて、**legacy tree と同じ scope tree を短く実行する executor**として扱える。

---

## 最初の実装 slice

### Patch 1: `ScopePlan` shadow + legacy materialize

まず実行はしない。

```rust
enum ScopePlanShadow {
    Planned {
        root: ScopePlanId,
        weighted_resume_steps: usize,
        root_marker_match: bool,
        request_boundary_class: RequestBoundaryClass,
        provider_child_count: usize,
    },
    Rejected(ScopePlanReject),
}
```

この段階で見るもの。

```text
scope_plan_candidates
scope_plan_planned
scope_plan_root_marker_match
scope_plan_root_marker_mismatch

scope_plan_provider_child_scopes
scope_plan_eval_frames
scope_plan_marker_lane_ops
scope_plan_request_lane_catch_same
scope_plan_request_lane_catch_foreign
scope_plan_request_lane_ref_set

scope_plan_materialize_tree_ok
scope_plan_materialize_tree_mismatch
```

合格条件はこれ。

```text
- root_marker_mismatch = 0
- materialize_tree_mismatch = 0
- planned が hot continuation の 40%以上を覆う
- ProviderEnv child scope の reject 理由が説明可能
```

「件数」じゃなくて **weighted by old resume steps** で見るのがいい。冷たい plan が大量に通っても意味は薄い。

---

### Patch 2: local lanes の interpreter を shadow 実行

まだ本実行に使わない。legacy tree と並べて、lane interpreter の結果を shadow 比較する。

比較対象は root marker だけだと足りない。

```text
- root marker
- request visibility
- handler boundary exposure
- provider grant gate
- generic fallback / routed yield / direct-tail 分類
- produced continuation shape の materialize 結果
```

ここで mismatch が出るなら、executor に進む前に止める。

---

### Patch 3: narrow executor 有効化

最初はこれだけ。

```text
ScopeKind::Root
  eval_lane
  marker_lane
  ProviderEnv child scope
    eval_lane
    marker_lane
    request_lane = None | CatchSameHandler
```

拒否条件は広くていい。

```rust
if !scope_plan.is_narrow_executable() {
    return execute_legacy_tree(...);
}
```

narrow executor の目的は「全部速くする」じゃなくて、**この構造が本当に wall time を削るかを測る**こと。

---

## 期待できる性能インパクト

| 段階                                         |          期待 |
| ------------------------------------------ | ----------: |
| ScopePlan shadow                           |          0% |
| lane shadow interpreter                    |       0〜微悪化 |
| narrow executor v1                         |   5〜12% くらい |
| ProviderEnv child + marker/request lane 拡張 | 15〜30% も狙える |
| その後の bytecode/block executor               |        さらに上 |

narrow executor v1 が 5% 未満でも即失敗とは限らない。
ただし、`continuation_resume_then_steps` / `marker_frame_entries` / `function_call_marker_plans` が落ちないなら、構造が刺さっていない可能性が高いねぇ。

---

## 監視する counter

既存 counter ではここ。

```text
continuation_resume_steps
continuation_resume_then_steps
continuation_resume_catch_steps
continuation_resume_marker_steps
continuation_resume_provider_steps
continuation_resume_force_steps

continuation_appends
continuation_append_steps
request_continuation_appends
direct_tail_continuation_appends
request_whole_continuation_appends

marker_frame_entries
function_call_marker_plans
active_marker_plan_pushes
active_marker_plan_dedupes
active_add_id_scans

catch_body_checks
catch_boundary_entries
catch_boundary_direct_tail_signals
catch_boundary_generic_request_signals

route_cert_provider_grant_dirty_add_id
route_cert_provider_grant_dirty_handler
route_cert_provider_grant_dirty_scope
```

追加したい counter はこれ。

```text
scope_plan_candidates
scope_plan_planned
scope_plan_rejected

scope_plan_weighted_resume_steps
scope_plan_weighted_planned_resume_steps

scope_plan_root_marker_match
scope_plan_root_marker_mismatch

scope_plan_provider_child_entries
scope_plan_provider_child_exits
scope_plan_provider_child_materialize_fallbacks

scope_lane_eval_steps
scope_lane_request_steps
scope_lane_marker_enter_ops
scope_lane_marker_exit_ops

scope_exec_hits
scope_exec_tree_fallbacks
scope_exec_shadow_mismatches
scope_exec_saved_resume_steps_estimate
```

特に見るべきはこの比率。

```text
scope_plan_weighted_planned_resume_steps / scope_plan_weighted_resume_steps
```

これが低いなら executor 化しても当たらない。

---

## やらない方がいい route

### flat trace 再挑戦

今はやめた方がいい。

flat trace が root marker で負けたなら、修正しても「線形列に scope の親子関係を暗黙エンコードする」方向になる。
それは最終的に scope tree を劣化コピーするだけになりそうだねぇ。

### marker-only rewrite

これも微妙。

`function_call_marker_plans` と `marker_frame_entries` は大きいけど、ProviderEnv child scope で初めて root marker が合ったなら、marker は単独原因じゃなくて **scope ownership の表面症状**だと思うよ〜。

### native close 追加

今は違う。

既存の native close は narrow cert がある時だけ安全で、ProviderEnv later grant は可視性が合っても実行形が遅かった、という記録がある。つまり次に安くするべきは cert 条件じゃなくて continuation / scope 表現だねぇ。

### bytecode へ直行

まだ早い。

ただし、scope-local lanes はそのまま bytecode/block executor の前段 IR になる。
だから「bytecode を捨てる」じゃなくて、**bytecode 化できる構造まで Evidence VM を整理する**のが良い流れ。

---

## rollback / stop 条件

即 rollback。

```text
- compare-control mismatch
- root_marker_mismatch > 0
- materialize_tree_mismatch > 0
- generic request fallback の分類が変わる
- ProviderEnv miss を invisible として扱う経路が出る
- any ProviderEnv grant 的な粗い判定が入る
- handler hygiene adversarial corpus が落ちる
```

方向転換を考える条件。

```text
- weighted planned coverage < 30〜40%
- narrow executor hit が多いのに wall time が 5% 未満しか改善しない
- continuation_resume_steps は落ちるが marker_frame_entries / active_add_id_scans が増えて相殺
- ProviderEnv child scope が nested / sibling crossing だらけで local lane として閉じない
```

その場合の次 route は flat trace ではなく、**prompt stack / scope stack 型の frame-loop executor**だと思う。
つまり別 route に行くとしても、方向はまだ「scope を first-class にする」側で、線形化へ戻る感じではないねぇ。

---

## 最終判断

**次は scope-local eval/request/marker lanes で narrow executor に進むべき**だよ〜。

ただし、名前は `ResumePlan` より `ScopePlan` / `ScopeLocalPlan` に寄せた方が安全そう。
今回の発見は「resume を平たく速くする」じゃなくて、**ProviderEnv が作る child scope の中でだけ eval/request/marker が正しく局所化できる**という発見に見える。

だから次の一手はこれ。

```text
ScopeTree を作る
各 scope に eval/request/marker lanes を持たせる
ProviderEnv は child scope として扱う
legacy materialize を残す
narrow executable な scope だけ実行する
```

これが一番、今回の成功結果を素直に伸ばせる構造だと思うよ〜。

---

## Implementation note: ScopePlan shadow v1

The first profile-only `ScopePlan` shadow has been implemented after this review.

Deep profile:

```text
nondet:
  scope_plan_candidates: 420
  scope_plan_planned: 420
  scope_plan_rejected: 0
  scope_plan_weighted_resume_steps: 21482
  scope_plan_weighted_planned_resume_steps: 21482
  scope_plan_root_marker_match: 420
  scope_plan_root_marker_mismatch: 0
  scope_plan_provider_child_scopes: 861
  scope_plan_eval_steps: 17660
  scope_plan_request_steps: 840
  scope_plan_marker_steps: 840
  scope_plan_child_marker_steps: 420
  scope_plan_request_lane_catch_foreign: 840
  scope_plan_legacy_tree_fallback_available: 420

showcase:
  scope_plan_candidates: 829
  scope_plan_planned: 829
  scope_plan_rejected: 0
  scope_plan_weighted_resume_steps: 31390
  scope_plan_weighted_planned_resume_steps: 31390
  scope_plan_root_marker_match: 829
  scope_plan_root_marker_mismatch: 0
  scope_plan_provider_child_scopes: 1787
  scope_plan_eval_steps: 23645
  scope_plan_request_steps: 1644
  scope_plan_marker_steps: 1678
  scope_plan_child_marker_steps: 856
  scope_plan_request_lane_catch_foreign: 1644
  scope_plan_legacy_tree_fallback_available: 829
```

Normal release keeps the sidecar disabled:

```text
scope_plan_candidates: 0
compare.control: match
```

Reading:

- Weighted planned coverage is 100% on the representative workloads.
- Root marker mismatch is 0, which supports the ProviderEnv child-scope split.
- All request lane entries are currently `CatchForeign`.

This means a narrow executor that only accepts `None | CatchSameHandler` would not hit the hot
workloads. The next useful slice is therefore not execution yet. It is a shadow comparison for
`CatchForeign` as a scope-local handler-boundary/request lane.
