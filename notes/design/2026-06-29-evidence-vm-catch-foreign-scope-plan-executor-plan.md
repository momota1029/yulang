# Evidence VM CatchForeign ScopePlan executor plan

## 1. Goal

Evidence VM の次の高速化として、`CatchForeign` を scope-local な
`BoundaryLane` として扱う `ScopePlan` executor を入れる。

`CatchForeign` は handler match ではなく、generic fallback でもなく、
provider permission cert でもない。signal dispatch では透明だが、
continuation から消せる境界ではない。

- `on_signal`: handler selection では透明。carried continuation へ catch boundary を
  preserved/pushed し、外側へ進む。
- `on_value`: legacy `CatchBody` と同じ value-resume behavior を実行し、その後外側へ進む。

executor を有効化する前に、legacy continuation semantics、handler hygiene、
provider permission invariants を壊していないことを shadow comparison と
adversarial corpus で確認する。

## 2. Current evidence

2026-06-29 時点の実装には、すでに次の surface がある。

- `EvidenceCatchBoundaryDeltaPlan`
- `EvidenceCatchBoundaryMode::{SameHandler, ForeignPassThrough, NoRoutedHandler}`
- `EvidenceCatchBoundarySignalClass`
- `EvidenceRequestDeltaPlan::catch_boundary_delta_plans`
- `EvidenceResumeScopedTracePlan`
- `EvidenceContinuationFrame::CatchForeignBoundarySegment`

deep profile の代表 workload では、first-class catch boundary delta shadow の mismatch は
0 と観測済み。

- `bench/nondet_20_discard.yu`
  - `scope_plan_catch_foreign_boundary_delta_signal_mismatch: 0`
  - `scope_plan_catch_foreign_boundary_delta_generic_fallback_mismatch: 0`
  - `scope_plan_catch_foreign_boundary_delta_materialized_shape_mismatch: 0`
  - `scope_plan_catch_foreign_boundary_delta_value_resume_mismatch: 0`
- `examples/showcase.yu`
  - `scope_plan_catch_foreign_boundary_delta_signal_mismatch: 0`
  - `scope_plan_catch_foreign_boundary_delta_generic_fallback_mismatch: 0`
  - `scope_plan_catch_foreign_boundary_delta_materialized_shape_mismatch: 0`
  - `scope_plan_catch_foreign_boundary_delta_value_resume_mismatch: 0`

`CatchForeignBoundarySegment` は、value resume で boundary ごとに
`continue_catch_body_result` を呼ぶ。signal 側も direct-tail / direct-abortive /
routed-yield / generic request を legacy semantics と同じ分類で通す。

残る対象は、segment 単体ではなく、`EvidenceResumeScopedTracePlan` の scope plan を
実行 gate として使い、eval lane、marker lane、ProviderEnv child scope、catch boundary lane
を scope-local に処理する narrow executor v1。

実装上は `EvidenceScopePlanBoundaryLane` で boundary lane を明示し、ProviderEnv
permission 側の `ProviderDirtyScopeCert` と、catch pass-through 側の
`ForeignCatchPassThroughCert` を分ける。narrow executor frame は実装済み。
frame 置換だけでは `continuation_resume_then_steps` しか下がらず、総 resume steps は
flat だった。次に有効化を狙う場合は、`EvidenceResumeScopedTracePlan` と
eval/request/marker/provider delta payload を使い、scope lane 自体を continuation tree
再帰なしで実行する必要がある。
2026-06-30 に direct-tail signal だけ、scope が request-boundary-free であることを
frame 作成時に記録し、scope continuation を一括 append して再帰的な boundary scan を飛ばす
fast path を試した。compare-control と shadow は一致したが、representative timing では
showcase 側が gate disabled より悪かったため、default gate は disabled のままにする。
その後、pass-through 時に `ScopePlanForeignCatchBoundary(scope, boundaries)` を compact tail
として preserved continuation へ積み、identity carried continuation では通常 append helper を
通さないようにした。この形では nondet が disabled control より 5% 以上改善し、showcase も
material regression しなかったため、default gate を enabled にする。
これは「delta payload executor」本体ではなく、next slice へ進む前の narrow signal fast path
として残す。
同日に scope-local value executor も実装して測定した。`CatchForeignBoundarySegment` /
nested `ScopePlanForeignCatchBoundary` を first-class `CatchForeign` action として扱い、
marker/provider child scope を保持した local plan は compare-control 上は一致した。
ただし代表 workload の通常 release path が material regression したため、
`SCOPE_PLAN_FOREIGN_CATCH_VALUE_EXECUTOR_ENABLED` は disabled にする。local plan の
materialization / reject / marker-provider scope preservation tests は残し、次に有効化する
場合は plan construction と eval lane dispatch の overhead を先に削る。

## 3. Non-goals

- later ProviderEnv grant native close を復活しない。
- nearest ProviderEnv miss を invisibility evidence として扱わない。
- arbitrary any ProviderEnv presence を permission evidence として扱わない。
- `Then` / `MarkerFrame` / `ProviderEnv` を scope-preserving invariant なしに flatten しない。
- `LexicalHandlerCandidate` や `HygieneFallback` を直接 `DirectHandlerCall` にしない。
- duplicate marker scope skip をもう一度入れない。
- broad stats-off refactor はこの task に含めない。
- bytecode/native backend へ飛ばない。

## 4. Soundness invariants

`CatchForeign` の透明性は dispatch だけに限る。continuation payload から boundary を
消してはいけない。

- `ForeignPassThrough` は `DirectTailResumptive` / `RoutedYield` / `GenericRequest` /
  `DirectAbortive` / `Unhandled` の signal kind を変えない。
- `CatchNoRouted` は generic fallback のまま。`CatchForeign` を generic fallback にしない。
- dirty provider grant classification は保持する。
- materialized continuation の shape digest は legacy と一致する。
  - `CatchBody` order
  - `MarkerFrame` order
  - `ProviderEnv` child scopes
  - `Then` ordering
  - `RefSet` boundaries
  - ordinary eval frame order
  - scope entry/exit order
- `ForeignPassThrough` は value resume 用に `catch_expr` / `arms` / `env` payload を保持する。
- direct-tail signal compact path は、carried signal の handler と一致する boundary を
  pass-through として扱わない。`boundary.catch_expr == signal.handler` が一つでもあれば
  legacy boundary path へ戻す。
- provider permission は ProviderEnv grant / handler ids / hygiene baseline から判定する。
  `CatchForeign` cert を provider permission evidence として使わない。
- provider dirtiness と foreign catch pass-through は別の意味として扱う。
  - `ProviderDirtyScopeCert`: provider/hygiene 側の dirty scope 証明。
  - `ForeignCatchPassThroughCert`: catch boundary が signal では透明、value では legacy
    `CatchBody` payload を持つ証明。

## 5. Implementation slices

### Stage A: Shadow comparison, no behavior change

既存 shadow comparison を保持し、executor gate へ進む前に mismatch 0 を再確認する。

- signal kind preservation
- generic fallback classification
- materialized continuation shape digest
- value-resume behavior

安全な fixture がない限り、value resume の runtime result を二重実行して比較しない。
payload digest と helper-level behavior を比較する。

### Stage B: BoundaryLane naming / representation

現在の request-lane-shaped surface を、boundary lane として読む。

```rust
enum EvidenceScopePlanBoundaryLane {
    None,
    Catch {
        same_handler: usize,
        no_routed_handler: usize,
        foreign_handler: usize,
    },
    RefSet {
        boundaries: usize,
    },
}
```

catch boundary deltas は現時点では `EvidenceRequestDeltaId` の delta list としてまとまって
いるため、単独 `CatchBoundaryDeltaId` / `RefSetBoundaryDeltaId` はまだ作らない。
ID を増やすだけの見かけの変換は避け、既存 delta table の責務に合わせる。

`EvidenceCatchBoundaryMode` はこのまま保持する。

- `SameHandler`
- `ForeignPassThrough`
- `NoRoutedHandler`

`ForeignPassThrough` は signal pass-through と value resume の両方を持つ。

### Stage C: Narrow ScopePlan executor v1

Stage A の shadow mismatch が全て 0 の場合だけ実装を有効にする。

受け入れ条件:

- one-shot continuation
- root marker match
- ProviderEnv child scope split ready
- all catch boundary deltas are `ForeignPassThrough`
- no `RefSet` boundary
- no `CatchNoRouted`
- no `SameHandler` handling in v1
- marker/provider deltas are represented or can materialize fallback safely
- legacy materialize fallback exists
- no legacy bridge
- no unrepresented resume_delta

実行:

- eval lane locally
- marker lane locally
- ProviderEnv child scopes locally
- `CatchForeign` on signal: append/preserve boundary delta into carried continuation and continue outward
- `CatchForeign` on value: execute legacy `CatchBody` value semantics and continue outward

fallback:

- unsupported shape は旧 continuation tree path へ戻す。
- mismatch counter が 0 でない場合は executor を有効化しない。

### Stage D: Executor counters

実行 gate と fallback 原因だけを narrow counters として追加する。
stats-off refactor には広げない。

## 6. Shadow comparison matrix

| Comparison | Legacy source | Planned source | Required result |
| --- | --- | --- | --- |
| signal kind preservation | `EvidenceRequestDeltaFrameKind` / legacy continuation classification | `EvidenceCatchBoundaryDeltaPlan::signal_class` | match |
| generic fallback classification | `CatchNoRouted` / unhandled request behavior | `EvidenceCatchBoundaryMode` | match |
| materialized shape digest | legacy `CatchBody` chain from request delta | `EvidenceCatchBoundaryMaterializedShapeDigest::from_deltas` | match |
| value-resume payload | `CatchBody { catch_expr, arms, env }` | `ForeignPassThrough { catch_expr, arms, env }` | match |
| provider permission | ProviderEnv grant and hygiene baseline | provider/hygiene cert only | no catch cert dependency |

## 7. Runtime counters

既存 counters:

- `scope_plan_catch_foreign_boundary_delta_signal_shadow`
- `scope_plan_catch_foreign_boundary_delta_signal_match`
- `scope_plan_catch_foreign_boundary_delta_signal_mismatch`
- `scope_plan_catch_foreign_boundary_delta_generic_fallback_shadow`
- `scope_plan_catch_foreign_boundary_delta_generic_fallback_match`
- `scope_plan_catch_foreign_boundary_delta_generic_fallback_mismatch`
- `scope_plan_catch_foreign_boundary_delta_materialized_shape_shadow`
- `scope_plan_catch_foreign_boundary_delta_materialized_shape_match`
- `scope_plan_catch_foreign_boundary_delta_materialized_shape_mismatch`
- `scope_plan_catch_foreign_boundary_delta_value_resume_shadow`
- `scope_plan_catch_foreign_boundary_delta_value_resume_match`
- `scope_plan_catch_foreign_boundary_delta_value_resume_mismatch`

追加する executor counters:

- `scope_exec_hits`
- `scope_exec_foreign_catch_hits`
- `scope_exec_tree_fallbacks`
- `scope_exec_signal_passthrough_hits`
- `scope_exec_value_resume_hits`
- `scope_exec_reject_not_one_shot`
- `scope_exec_reject_root_marker_mismatch`
- `scope_exec_reject_non_foreign_catch`
- `scope_exec_reject_ref_set`
- `scope_exec_reject_missing_materialize_fallback`
- `scope_exec_reject_shape_mismatch`

## 8. Validation commands

Required:

```text
cargo fmt --all --check
cargo check -q -p evidence-vm -p yulang
cargo check -q --release -p evidence-vm -p yulang
cargo build -q --release -p yulang
cargo test -q -p evidence-vm -- --test-threads=1
cargo test -q -p yulang runtime_evidence -- --test-threads=1
tests/yulang/yulang-adversarial-corpus/probe.sh
```

Representative runtime checks:

```text
target/release/yulang debug evidence-vm-run --compare-control bench/nondet_20_discard.yu
target/release/yulang debug evidence-vm-run --compare-control --runtime-evidence-profile-deep bench/nondet_20_discard.yu
target/release/yulang debug evidence-vm-run --compare-control examples/showcase.yu
target/release/yulang debug evidence-vm-run --compare-control --runtime-evidence-profile-deep examples/showcase.yu
target/release/yulang run --runtime-phase-timings --print-roots bench/nondet_20_discard.yu
target/release/yulang run --runtime-phase-timings --print-roots examples/showcase.yu
```

記録するもの:

- exact commit / branch
- exact commands
- nondet timings
- showcase timings
- compare-control results
- shadow mismatch counters
- scope_exec counters
- rollback/keep decision

## 9. Stop / rollback criteria

即 stop / rollback:

- `compare-control` mismatch
- adversarial corpus mismatch
- handler hygiene regression
- generic request fallback behavior changes
- direct-tail が generic request へ予期せず変わる
- routed-yield が generic request へ予期せず変わる
- ProviderEnv miss を invisibility として使う
- any ProviderEnv を permission evidence として使う
- native close shadow mismatch
- catch_foreign shadow mismatch counter が 1 以上

keep 条件:

- compare-control と adversarial checks が pass
- shadow mismatches が 0
- `scope_exec_foreign_catch_hits > 0` が representative workload で出る
- `runtime_evidence_execute` が代表 workload の片方で約 5% 以上改善
- 他方の代表 workload と小さい examples が material regress しない
- `continuation_resume_*` が down または flat
- generic request signals が増えない
- direct-tail signals が予期せず減らない

改善が nondet/showcase の両方で 5% 未満で、複雑性だけが増える場合は executor を disabled
または rollback する。設計ノートと shadow counters は有用なら残す。
