# ChatGPT Pro consultation answer: local mutable ref and loop runtime plan

## 結論

VM レベルの `LocalRefCell` は、**そのままの共有 mutable cell として入れるなら危険**である。一方で、`LocalRefCell` という発想を「compiler-generated local state handler の runtime 表現」として言い換えるなら、方向性はかなりよい。

推奨する名前と構造は、裸の `LocalRefCell` ではなく次である。

```text
KnownHandlerPlan::State
  -> RuntimeStateHandlerFrame
  -> StateRef token
  -> DirectStateGet / DirectStateSet
```

重要なのは、最適化対象を「local variable」や「`for` body」ではなく、**証明済みの state-like handler** に置くことである。最初の producer が compiler-generated local mutable variable であることは問題ない。ただし runtime が `my $x`、`std.control.var.ref`、`get`/`set` という source name や record field shape を直接見始めると、すぐに special case が積み上がる。

したがって、短く言うと次になる。

```text
bad:
  local var syntax -> Rc<RefCell<Value>> に置換
  escaped &x は cell pointer
  continuation はあとで辻褄合わせ

good:
  compiler-generated var.run に certificate
  Evidence VM が KnownHandlerPlan::State を作る
  runtime は active StateHandlerFrame に状態を持つ
  &x は storage ではなく StateRef capability token
  continuation capture/resume は state frame を snapshot/fork
```

2 秒の問題に対する近道は存在する。だが、それは downstream patch ではなく、`var.get` / `var.set` / `RefSet` が generic effect protocol を通っている原因側を段階的に外すことだ。

---

## 1. 測定値から読むべきこと

現在の測定はかなりはっきりしている。

```text
recursive sum loop:
  約 1.4ms - 1.6ms

recursive list loop:
  約 1.7ms - 1.9ms

std for without local ref:
  約 6ms

std for + local ref sum:
  約 1.8s - 2.0s

std for + local ref push:
  約 1.8s - 2.0s

nondet list:
  約 10ms
```

ここから読むべき主因は次である。

```text
pure recursion is fine
std for has overhead, but not catastrophic
local mutable ref update through public ref protocol is catastrophic
```

`for` そのものを最初に高速化するのは順序が悪い。`for_no_ref` が 6ms である以上、`for` を完全に消しても 2 秒の大半は残る。逆に local mutable ref update を direct 化できれば、`for` はまだ 6ms 級の通常問題に戻る。

現行 lowering で 1 回の assignment が通る道は次である。

```text
&total = $total + i + j

reference evaluation
  -> record field selection
  -> update_effect() call
  -> ref_update::update request
  -> var.get request
  -> var.set request
  -> catch/resume machinery
  -> handler recursion
```

これは「state slot に値を書くだけ」に対して過剰に一般的である。ただし public `std.control.var.ref` はこの一般性が必要なので、一般 protocol を壊すのではなく、**証明済み local state ref だけが protocol の内側から短絡できる**ようにするのが正しい。

---

## 2. `LocalRefCell` は正しい方向か

### 2.1 raw `LocalRefCell` は危険

次のような表現は避けたい。

```rust
Value::LocalRefCell(Rc<RefCell<Value>>)
```

これをそのまま escaped `&x` の実体にすると、captured continuation / multi-shot resume で semantic bug が出る。

例えば state handler semantics では次が自然である。

```text
x = 10
capture k
resume k -> branch A starts with x = 10
branch A sets x = 20
resume k -> branch B starts with x = 10
```

しかし `Rc<RefCell<Value>>` を continuation 間で共有すると、branch A の `x = 20` が branch B に漏れる。これは state handler の再帰的実装と違う。Yulang が algebraic effects と multi-shot continuation を言語機能として持つなら、ここは曖昧にできない。

### 2.2 continuation-aware cell なら viable

`LocalRefCell` を次の意味で定義するなら viable である。

```text
Local state is not a heap cell.
Local state is a slot in the active state handler frame.

&x is not the storage itself.
&x is a capability token that resolves to the active frame.
```

runtime representation はこう置くのがよい。

```rust
enum RuntimeKnownHandlerFrame {
    State(RuntimeStateHandlerFrame),
}

struct RuntimeStateHandlerFrame {
    plan_id: EvidenceVmKnownHandlerPlanId,
    handler_id: u32,
    state_slot: StateSlotId,
    state_def: DefId,
    value: Value,
    continuation_semantics: StateContinuationSemantics,
}

enum StateContinuationSemantics {
    SnapshotFork,
}

enum RefRepr {
    StateSlot(StateRef),
    Generic(Value),
    Projection(ProjectionRef), // later
}

struct StateRef {
    plan_id: EvidenceVmKnownHandlerPlanId,
    handler_id: u32,
    state_slot: StateSlotId,
    scope_id: StateScopeId,
}
```

この設計なら、`&x` は関数や record に escape しても「active state frame を探す token」として正しく振る舞える。scope 外に出た後で使われた場合は、現在の generic behavior に合わせて fallback か unhandled/runtime error にする。勝手に heap cell として延命しない。

---

## 3. captured continuation / multi-shot resume の意味論

推奨 semantics は **snapshot/fork** である。

```text
continuation capture:
  active RuntimeStateHandlerFrame を continuation snapshot に含める

resume:
  snapshot から state frame を復元する

multi-shot resume:
  resume ごとに state frame を fork する

set:
  現在 branch の state frame だけを書き換える
```

これにより、handler recursion で表現していた local state と同じ意味を保てる。

### 3.1 one-shot destructive reuse は後回し

将来、one-shot continuation が証明できるなら、snapshot を clone せず move/reuse する最適化はあり得る。

```text
if continuation is proven one-shot:
  frame can be reused destructively
else:
  fork frame on resume
```

ただし最初から one-shot 前提にしない方がよい。local ref の correctness canary が multi-shot を含むなら、最初は常に snapshot/fork で実装するべきである。

### 3.2 shared-cell semantics を入れるなら別機能

もし将来「本当に共有 heap cell」が欲しいなら、それは local mutable var ではなく別 primitive として入れるべきである。

```text
State handler local var:
  snapshot/fork

Explicit shared cell primitive:
  shared mutation across continuation branches, if language chooses to expose it
```

この 2 つを混ぜると、effect handler の state semantics が壊れる。

---

## 4. 実装場所: lowering 変更か、intrinsic か、pattern specialization か、new IR か

最初にやるべきなのは、source lowering を全面変更することではない。既存の `var_ref/run` lowering を truth surface として残し、compiler が生成した local var handler に **certificate** を付けるのが安全である。

推奨分担は次。

```text
lowering:
  compiler-generated local var handler に certificate を付ける

specialize / runtime evidence surface:
  effect family / operation / handler identity を保持する

Evidence VM plan:
  certificate と route proof を突き合わせて KnownHandlerPlan::State を作る

runtime:
  known state catch に RuntimeStateHandlerFrame を張る
  certified get/set を direct 実行する

later control IR:
  DirectStateGet / DirectStateSet / KnownOperationCall を入れる
```

### 4.1 source path や std 名で認識しない

避けるべき判定は次。

```text
path == std.control.var.ref
field name == update_effect
operation name == get / set
source var name starts with #
benchmark file path matches loop_for_sum_ref
```

代わりに、内部 identity を使う。

```rust
struct LocalStateHandlerCertificate {
    synthetic_var_id: SyntheticLocalVarId,
    handler_expr: ExprId,
    family_id: EffectFamilyId,
    get_operation_id: OperationId,
    set_operation_id: OperationId,
    state_def: DefId,
}
```

今の compiler が local mutable var lowering を生成しているなら、最初の producer は compiler 自身でよい。任意 user handler の source shape recognition は後回しにする。

### 4.2 pattern specialization は「compiler certificate + verifier」だけ許す

`var.run` と似た形の arbitrary user code を VM が勝手に state handler とみなすのは危険である。同じ型・同じ row でも、次の handler があり得る。

```text
set を無視する
get 時に log を出す
continuation を 2 回呼ぶ
continuation を保存する
別 handler へ forward する
```

最初は次だけを認める。

```text
source = CompilerGeneratedLocalVar
handler has exactly get/set for one family
get arm tail-resumes exactly once with current state
set arm tail-resumes exactly once with new state and unit
continuation does not escape
no guards
no delayed/callback boundary around continuation use
```

### 4.3 new control IR は「最終形」、最初は VM plan でよい

理想の最終形はこうである。

```rust
enum EvidenceVmOperationExecutionPlan {
    DirectStateGet { plan_id: EvidenceVmKnownHandlerPlanId },
    DirectStateSet { plan_id: EvidenceVmKnownHandlerPlanId },
    DirectAbortive,
    DirectTailResumptive,
    YieldFallback,
    BlockedFallback,
    GenericFallback,
}
```

または、より一般化してこうする。

```rust
enum EvidenceVmOperationExecutionPlan {
    KnownOperationCall(KnownOperationExecutionPlan),
    DirectAbortive,
    DirectTailResumptive,
    YieldFallback,
    BlockedFallback,
    GenericFallback,
}

enum KnownOperationExecutionPlan {
    StateGet { plan_id: EvidenceVmKnownHandlerPlanId },
    StateSet { plan_id: EvidenceVmKnownHandlerPlanId },
}
```

最初は Rust enum を増やすだけでもよい。source/control IR へ `DirectStateGet` を出すのは、plan/runtime canary が揃ってからで十分である。

---

## 5. escaped refs の表現

escaped `&x` は、storage ではなく `StateRef` token として表現する。

```text
&x evaluates to:
  StateRef(plan_id, handler_id, state_slot, scope_id)
```

この token を使う時に active frame を解決する。

```text
StateRef.get:
  active RuntimeStateHandlerFrame を plan_id / handler_id / scope_id で探す
  見つかれば value を読む
  見つからなければ generic fallback または current behavior と同じ error

StateRef.set:
  同じ frame lookup
  現在 branch の frame.value を更新する
```

これにより、次が両立できる。

```text
&x passed into function:
  same dynamic extent なら fast

&x stored in record/tuple/list:
  same dynamic extent なら fast

&x returned outside run scope:
  active frame がないので、generic/current behavior に従う

user/file/projected refs:
  StateRef でないので generic protocol
```

### 5.1 generic `std.control.var.ref` との接続

public `std.control.var.ref` は壊さない。runtime 側で ref value の表現を分けるだけである。

```rust
enum Value {
    Ref(RefRepr),
    Record(...),
    Closure(...),
    ...
}

enum RefRepr {
    StateSlot(StateRef),
    Generic(Value),
}
```

generic code が `r.get()` や `r.update(f)` を呼ぶ場合、`r` が `StateSlot` なら fast path、そうでなければ既存 protocol へ落とす。これなら public API は普通の ref のままであり、VM は認証済み receiver だけを速くする。

---

## 6. projected refs と `ref_update`

projected refs は最初の stage に混ぜない方がよい。

`ref_update` は、record/list/string の一部を focused update するために必要な protocol である。例えば projected ref は概念的にこう動く。

```text
old_base = base.get()
old_focus = projection.read(old_base)
new_focus = f(old_focus)
new_base = projection.write(old_base, new_focus)
base.set(new_base)
```

この順序は、単純な local state slot assignment よりずっと繊細である。`f` の評価中に effect が起きる、continuation が capture される、projection chain が nested する、といったケースがある。

したがって最初はこう分ける。

```text
Stage local state:
  StateRef get/set/direct assignment only

Stage projection later:
  ProjectionRef(base_ref, ProjectionPlan)
  base_ref may be StateRef or Generic
  read/evaluate/write order canaries を先に追加
```

`&xs.push(i + j)` が遅いからといって list projection/builder を先に触るのは危ない。`loop_for_20_discard` は local state + ref protocol + list merge が混ざっている。先に local state/ref を抜くと、list merge の真の重さが見える。

---

## 7. staged implementation plan

### Stage 0: counters and semantic canaries

挙動変更なし。

追加 counters:

```text
ref_set_evals
ref_set_update_effect_calls
ref_set_assignment_ref_update_requests
ref_set_value_ref_update_requests
local_state_handler_candidates
local_state_handler_certificates
known_state_handler_plans
known_state_get_requests
known_state_set_requests
state_ref_values_created
```

canaries:

```text
single local var read/write
two locals updated interleaved
shadowed local vars
local ref escapes into closure and record
local ref returned outside scope matches current behavior
user ref remains generic
file ref remains generic
projected ref remains generic
nondet around local update
continuation captured before/after update and resumed twice
same operation names in different hygienic families do not collide
blocked handler route does not direct execute
```

Rollback:

```text
no behavior change, only counters/debug output
```

### Stage 1: compiler certificate + KnownHandlerPlan::State, plan-only

Compiler-generated local mutable var lowering emits a certificate. Evidence VM consumes it and prints/debugs the known handler plan, but runtime still uses generic path.

Data:

```rust
enum KnownHandlerPlan {
    State(StateHandlerPlan),
}

struct StateHandlerPlan {
    plan_id: KnownHandlerPlanId,
    handler_expr: ExprId,
    state_def: DefId,
    family: EffectFamilyId,
    get_op: OperationId,
    set_op: OperationId,
    source: StateHandlerSource,
    continuation: StateContinuationSemantics,
}

enum StateHandlerSource {
    CompilerGeneratedLocalVar(SyntheticLocalVarId),
}
```

Acceptance:

```text
local mutable var program produces one StateHandlerPlan per local ref
user/file/projected refs produce no StateHandlerPlan
all existing tests pass
```

Rollback:

```text
ignore KnownHandlerPlan at runtime
```

### Stage 2: RuntimeStateHandlerFrame, but no request-free call site yet

Known state handler entry creates a runtime frame.

```text
enter var.run:
  push RuntimeStateHandlerFrame(value = initial state)
  eval body
  pop frame
```

At catch boundary, if a request is certified `get` / `set` for that handler, execute against the state frame instead of evaluating the handler arm body.

This is still late. It does not remove request allocation, but it removes handler recursion and is likely enough to reduce the 2-second case substantially.

Counters:

```text
known_state_frame_entries
known_state_frame_exits
known_state_direct_gets_late
known_state_direct_sets_late
known_state_direct_missing_frame
known_state_direct_non_resumptive
known_state_direct_hygiene_rejects
```

Acceptance:

```text
2-second local-ref loop drops by a large factor
compare-control / canaries match
no direct path for user/file/projected refs
```

Rollback:

```text
gate off -> eval original handler arms
```

### Stage 3: continuation snapshot/fork for state frames

Before enabling broader direct state execution, state frames must be part of continuation snapshots.

Implementation:

```text
StoredContinuation includes active state frame snapshot
resume installs forked state frames
multi-shot resume clones/forks frame values
```

Counters:

```text
known_state_frame_snapshots
known_state_frame_forks
known_state_frame_multishot_forks
known_state_frame_one_shot_reuses  // later, likely zero first
```

Acceptance:

```text
capture/resume local state canaries pass
nondet around local update matches generic behavior
```

Rollback:

```text
disable direct state execution if snapshot/fork canaries fail
```

### Stage 4: route-specific DirectStateGet / DirectStateSet

Now move from late catch-boundary optimization to call-site direct execution.

Plan condition:

```text
operation call route proves handler H is visible
H has KnownHandlerPlan::State P
operation is P.get or P.set
route is not blocked/delayed/callback-unsafe
```

Runtime execution:

```text
DirectStateGet:
  find active StateHandlerFrame by plan_id/handler_id
  return frame.value

DirectStateSet(new):
  evaluate new first, preserving existing order
  find active StateHandlerFrame
  frame.value = new
  return ()
```

Counters:

```text
plan_direct_state_get_ops
plan_direct_state_set_ops
direct_state_get_calls
direct_state_set_calls
direct_state_frame_hits
direct_state_frame_misses
direct_state_hygiene_rejects
direct_state_generic_fallbacks
direct_effect_calls
```

Acceptance:

```text
direct_effect_calls increases for certified local state get/set
late catch-boundary direct counters decrease
2-second case remains fixed or improves further
```

Rollback:

```text
execution plan remains in debug output, runtime falls back to generic request
```

### Stage 5: `RefSet` fast path for `StateRef`

This is the stage that turns assignment into an actual local state write.

Current assignment uses:

```text
reference -> update_effect -> ref_update::update -> get -> set
```

For `StateRef`, shortcut to:

```text
evaluate reference
evaluate assigned value
if reference is StateRef and active frame visible:
  frame.value = assigned
  return ()
else:
  generic RefSet path
```

Counters:

```text
ref_set_state_ref_candidates
ref_set_state_ref_direct_sets
ref_set_state_ref_frame_misses
ref_set_state_ref_hygiene_rejects
ref_set_state_ref_generic_fallbacks
ref_set_protocol_calls_saved
```

Acceptance:

```text
local assignment avoids update_effect/ref_update for StateRef
user/file/projected refs still use generic protocol
assignment value effect order canaries pass
```

Rollback:

```text
StateRef remains a value, but RefSet ignores its fast path
```

### Stage 6: escaped `StateRef` receiver get/set

Generic code receiving `&x` can remain fast.

```text
fn f(r) = r.get()
f(&x)
```

If `r` is `StateRef`, direct get. If not, generic method call.

Counters:

```text
state_ref_receiver_get_candidates
state_ref_receiver_set_candidates
state_ref_receiver_direct_gets
state_ref_receiver_direct_sets
state_ref_receiver_fallback_no_active_frame
state_ref_receiver_fallback_generic_ref
```

Rollback:

```text
StateRef receiver methods use generic record/ref behavior
```

### Stage 7: `StateRef.update(f)`

Only after get/set and assignment are stable.

Correct order:

```text
old = read frame.value
new = evaluate f(old) in same dynamic context
write frame.value = new only after f returns normally
```

Canaries:

```text
f throws effect before return -> state unchanged
f captures continuation -> resume branches isolate state
f resumes multiple times -> no shared mutation leak
nested update -> order preserved
```

Rollback:

```text
r.update(f) uses existing ref_update protocol
```

### Stage 8: ProjectionRef / lens plan

Add structural projection after local StateRef is stable.

```rust
enum RefRepr {
    StateSlot(StateRef),
    Projection { base: Box<RefRepr>, plan: ProjectionPlan },
    Generic(Value),
}
```

This allows projected refs to become faster without pretending they are simple cells.

### Stage 9: std `for` / iterator IR

Only after local refs are no longer catastrophic.

Safe route:

```text
lowering emits LoopPlan / IteratorPlan certificate
VM executes certified loop shape directly
fallback keeps generic std for
```

Avoid matching `std.for` by name. Use compiler/lowering identity or checked iterator shape.

---

## 8. Near-term optimization: yes, but keep it principled

There is a smaller near-term optimization that is safe and likely to reduce the 2-second case substantially:

```text
compiler certificate
  -> KnownHandlerPlan::State
  -> late catch-boundary direct get/set
```

This is not the final architecture, because it still allocates effect requests and still goes through catch/resume. But it is a good first slice because:

```text
- it preserves existing source lowering
- it does not alter public ref abstraction
- it uses certificate identity, not source names
- it can be gated off
- it proves the state-handler representation before call-site direct ops
```

The second near-term optimization is `RefSet` direct assignment to `StateRef`, but that should wait until state frames and continuation snapshot/fork are solid. It has bigger performance upside, but also bigger semantic surface.

Avoid tiny benchmark patches such as:

```text
if file == loop_for_sum_ref_20_discard then shortcut
if callee name ends with update_effect then direct
if record has fields get/update_effect then assume ref
if path string is std.control.var.ref then assume local cell
```

These will make later projected refs and user refs painful.

---

## 9. Handler hygiene / marker / provider semantics

Direct state access must preserve this invariant:

```text
A direct state operation may access only the active state frame
belonging to the same handler/capability that the evidence route proves visible.
```

Runtime lookup should use ids, not names.

```text
lookup key:
  plan_id
  handler_id or capability_id
  allowed_set_id / provider grant permission
  active frame scope
```

Direct path rejects if:

```text
route is blocked
route crosses delayed/callback boundary without explicit evidence
provider grant is dirty under current marker/provider state
active frame not found
handler id mismatch
operation role mismatch
```

Counters should distinguish these reasons. A single `fallback` counter is not enough.

```text
direct_state_reject_blocked_route
direct_state_reject_delayed_boundary
direct_state_reject_callback_boundary
direct_state_reject_provider_dirty_scope
direct_state_reject_provider_dirty_add_id
direct_state_reject_provider_dirty_handler
direct_state_reject_missing_frame
direct_state_reject_wrong_handler
```

---

## 10. Tests and invariants before behavior changes

### Local state basics

```text
read initial state
write then read
two writes in sequence
two independent locals updated interleaved
shadowed locals do not collide
nested handlers with same operation names do not collide
```

### Escaping

```text
&x passed to function and read
&x passed to function and assigned
&x stored in record and used inside scope
&x stored in list/tuple and used inside scope
&x returned outside scope preserves current behavior
closure captures &x and is called inside scope
closure captures &x and is called after resume
```

### Generic refs

```text
user-defined ref remains generic
file ref remains generic
record projected ref remains generic
list/string projected ref remains generic
record-shaped value with get/update_effect is not treated as StateRef unless certified
```

### Continuation and nondet

```text
capture before update, resume twice
capture after update, resume twice
nondet branches update same local, no branch leaks into another
StateRef captured in closure remaps to resumed frame
multi-shot resume does not share raw cell mutation
```

### Evaluation order

```text
assignment reference evaluated before assigned value, if that is current behavior
assigned value effect occurs before write
assigned value abort/unhandled means no write
update(f) writes only after f returns normally
projection update preserves read/evaluate/write order
```

### Hygiene

```text
blocked route never direct executes
delayed/callback boundary falls back
same operation path in different hygienic family does not collide
provider grant direct path rejects when dirty
```

---

## 11. Ranking of options

| Option | Semantic risk | Expected gain | Implementation size | Fit with algebraic effects | Recommendation |
|---|---:|---:|---:|---:|---|
| Raw `Rc<RefCell<Value>>` `LocalRefCell` | Very high | High | Medium | Low | Avoid |
| Continuation-aware `RuntimeStateHandlerFrame` | Medium | High | Medium | Very high | Do |
| Compiler certificate for local var state handler | Low | Enables gain | Small-medium | Very high | Do first |
| Late catch-boundary direct get/set | Low-medium | High for 2s case | Medium | High | Good first execution slice |
| Route-specific `DirectStateGet/Set` | Medium | Medium-high | Medium | Very high | Do after frame/canaries |
| `RefSet` direct assignment to `StateRef` | Medium | Very high | Medium | High if certified | Do after state frame |
| Escaped `StateRef` receiver get/set | Medium | Medium-high | Medium | High | Later |
| `StateRef.update(f)` | High | Medium-high | Large | Medium-high | Later with canaries |
| Projection/lens ref plan | High | Medium | Large | High if carefully staged | Defer |
| std `for` LoopPlan | Medium | Medium | Medium | Orthogonal | After local refs |
| Matching std paths / field names / benchmark files | Very high | Short-term | Small | Very low | Avoid |
| Arbitrary user handler shape recognition | Very high | Uncertain | Large | Risky | Avoid until explicit certificates |

---

## 12. Direct answers to the questions

### 1. Is VM-level `LocalRefCell` right or dangerous?

A raw shared `LocalRefCell` is dangerous. A continuation-aware state frame with `StateRef` token is the right direction. The architecture should be known state handler specialization, not local variable special casing.

### 2. What semantics under captured continuations / multi-shot resume?

Snapshot/fork. Captured continuations include state frame snapshots. Multi-shot resume forks those frames. Direct writes affect only the current branch. One-shot destructive reuse is a later optimization after proof.

### 3. Implement by lowering, intrinsic, pattern specialization, or new IR?

Do not replace the source semantics wholesale. Add compiler certificates to existing local var lowering, carry them through specialize/evidence, build `KnownHandlerPlan::State`, then add runtime state frames and direct op execution. New `DirectStateGet/Set` IR is the eventual call-site execution form. Arbitrary pattern specialization is not first-stage work.

### 4. Escaped refs representation?

`&x` becomes `StateRef(plan_id, handler_id, slot, scope)` rather than a storage cell. It resolves to an active runtime state frame when used. If no matching frame exists, fallback/error according to current semantics. Generic refs remain generic.

### 5. Projected refs interaction?

Keep projected refs on `ref_update` initially. Later introduce `ProjectionRef(base, ProjectionPlan)`, where base may be `StateRef`. Preserve read/evaluate/write order and continuation behavior. Do not treat projections as simple local cells.

### 6. Implementation stages and rollback?

Use the stages above: counters/canaries, certificate plan-only, runtime state frame, snapshot/fork, direct get/set, `RefSet` StateRef assignment, escaped receiver fast path, update(f), projection, loop IR. Every stage gets a feature gate that falls back to existing generic protocol.

### 7. Invariants/tests?

Add local state, escaping, generic refs, continuation/multi-shot, evaluation order, and hygiene canaries before enabling default behavior. Especially test multi-shot state isolation before any cell-like representation ships.

### 8. Smaller near-term optimization?

Yes. Known state handler late direct get/set is a safe first execution slice and should cut the 2-second case substantially. It is not a benchmark trick if driven by compiler certificate + handler identity. `RefSet` StateRef shortcut is the next bigger win, but should wait until state frame semantics are pinned.

### 9. Should std `for` be optimized after local refs?

Yes, after local refs. The safe route is a compiler/lowering-certified loop/iterator plan, not matching `for` by std name. Current data says `for` overhead is real but secondary.

---

## 13. Attractive paths to avoid

### 13.1 Raw heap cell for local vars

Fast but wrong under multi-shot unless wrapped in snapshot/fork machinery. Once wrapped, it is no longer a simple heap cell; it is a state frame.

### 13.2 Path/name matching

`std.control.var.ref`, `update_effect`, `get`, `set`, benchmark file names, and source variable names are not proof. Use internal ids and certificates.

### 13.3 Record-shape recognition for refs

A record with `get` and `update_effect` is not necessarily a local ref. It may be user code, file state, logging, validation, projection, or effectful logic.

### 13.4 Optimizing `update(f)` too early

`update(f)` has evaluation-order and continuation subtleties. Direct assignment is much simpler. Do assignment first.

### 13.5 Optimizing list builder before local ref

`&xs.push` is slow, but it combines local state, ref protocol, and list merge. Fix local state/ref first, then measure builder/list separately.

### 13.6 Optimizing std `for` before local ref

`for` is slower than handwritten recursion, but not the 2-second catastrophe. Fix state/ref first.

---

## 14. Recommended near-term target

The first concrete target should be:

```text
compiler-generated local var certificate
  -> KnownHandlerPlan::State
  -> RuntimeStateHandlerFrame
  -> late direct get/set at catch boundary
  -> snapshot/fork canaries
```

Then move to:

```text
DirectStateGet/Set at operation call site
  -> StateRef direct RefSet assignment
```

Expected performance shape:

```text
before:
  for + local ref: ~2s

after late known-state get/set:
  likely tens of ms rather than seconds

after DirectStateGet/Set:
  lower again, but RefSet protocol may still dominate

after StateRef RefSet direct assignment:
  should approach std for without refs, plus arithmetic/ref overhead

after LoopPlan:
  std for gap vs handwritten recursion can be addressed
```

The design stays principled if every fast path is justified by:

```text
handler meaning certificate
+ route/visibility proof
+ active frame guard
+ continuation snapshot/fork semantics
```

That is the difference between a maintainable Evidence VM optimization and a local-variable-only runtime hack.
