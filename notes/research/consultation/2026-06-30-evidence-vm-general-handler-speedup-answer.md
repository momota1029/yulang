# ChatGPT Pro answer: Evidence VM general handler speedup after known-state

## 結論

次の本命は、**late catch-boundary direct state execution の延長ではなく、operation call site 側に `KnownOperationCall` を作り、その最初の実行形として `DirectStateGet` / `DirectStateSet` を持たせること**である。

ただし、実装順としては次の 2 つを分けるべきである。

```text
semantic storage:
  RuntimeKnownHandlerFrame::State / RuntimeStateHandlerFrame

call-site execution:
  EvidenceVmOperationExecutionPlan::DirectStateGet
  EvidenceVmOperationExecutionPlan::DirectStateSet
```

現在の実装は、operation request が generic に作られ、catch boundary まで届いた後に handler arm 評価だけを短絡している。これは最初の 2 秒級の破局を止めるには正しいが、architecture の最終形ではない。`direct_effect_calls == 0` で operation object が `generic-fallback` のままなら、hot path はまだ「effect request を作る」「continuation を持ち回る」「catch/resume の境界を通る」という経路にいる。

次の原則はこう置くのがよい。

```text
KnownHandlerPlan::State
  proves handler meaning

Evidence route / operation visibility
  proves this call reaches that handler under current hygiene

KnownOperationCall
  intersects both proofs at a concrete operation call site

RuntimeStateHandlerFrame
  stores dynamic state and participates in continuation snapshot/fork

DirectStateGet/Set
  executes request-free only when the active frame and visibility proof match
```

これなら「local variable 専用セル」ではなく、「証明済み known handler operation の request-free execution」という一般機構になる。最初の producer が compiler-generated local mutable variable であることは問題ではない。問題になるのは、proof surface を通さずに `my $x` や `std.control.var.ref` の path/name/record shape を VM が直接見始めることである。

---

## 1. 現状の 50ms local-ref sum で何が残っているか

最もありそうな残コストは、単一のボトルネックではなく次の層の合算である。

```text
&total = $total + i + j

1. RefSet node evaluation
2. reference expression evaluation
3. public ref protocol:
     update_effect
     ref_update
4. state get operation
5. state set operation
6. generic effect request / catch / resume machinery
7. env clone / frame append / marker/provider bookkeeping
```

現在の counters はかなり示唆的である。

```text
loop_for_no_ref_20_discard:
  runtime_execute: 6.4ms
  expr_evals:      49077
  env_clones:      33120

loop_for_sum_ref_20_discard:
  runtime_execute: 50.3ms
  expr_evals:      58718
  env_clones:      52815
  known_state_direct_gets: 800
  known_state_direct_sets: 400
  ref_set_evals: 400
  ref_set_update_effect_calls: 400
  ref_set_assignment_ref_update_requests: 400
```

`expr_evals` は約 1.2 倍にしか増えていない。一方で時間は約 8 倍である。したがって、主因は単純な式評価回数ではない。`Env` が persistent one-binding chain であるなら、`env_clones` も「大きな HashMap 全コピー」ではないが、continuation/frame/request を通るたびに clone と append が増えるので、protocol cost の症状として見える。

特に重要なのは、`known_state_direct_gets/sets` が増えているのに `direct_effect_calls` が 0 の点である。これは、`get` / `set` の handler arm body は飛ばせているが、operation call 自体はまだ direct route になっていないという意味である。つまり今の direct execution は **handler execution optimization** であって、まだ **operation dispatch optimization** ではない。

50ms の内訳の読みは次である。

```text
primary:
  RefSet / update_effect / ref_update protocol layer
  + get/set operation request creation
  + catch/resume boundary traversal

secondary:
  env clone and frame append churn caused by the above

not primary yet:
  list_merge
  std for iterator overhead
  generic continuation executor work alone
```

`&xs.push` がさらに遅いのは list merge が加わるからである。ただし `nondet` は似た数の `list_merge_calls` を持ちながら 10ms 程度で走っているので、list merge だけを先に触るのは読み違いになりやすい。

---

## 2. late catch-boundary direct state execution は十分か

十分ではない。位置づけは「Stage 2 の正しい stopgap」である。

late catch-boundary direct state execution は次を削る。

```text
request reaches catch
  -> handler arm matching
  -> arm body eval
  -> handler recursion expression eval
```

しかし次は削らない。

```text
operation value application
operation request allocation
payload wrapping
continuation capture / append
request propagation to catch
visibility/catch dispatch path
RefSet -> update_effect -> ref_update protocol
```

したがって、local-ref catastrophe を止めるには十分でも、「`for` without refs との差を詰める」には足りない。`direct_effect_calls` が 0 のままなら、この層が残っていると見るべきである。

次の stage では、少なくとも certified `get` / `set` call site について、generic request を作る前に次へ落とす必要がある。

```text
get():
  state = active_state_frame[plan_id].state
  return state

set(new):
  active_state_frame[plan_id].state = new
  return ()
```

ただしここで「runtime env の DefId を直接書き換える」という方向へ行くと壊れる。route-specific direct state op は、状態の実体が `RuntimeStateHandlerFrame` にあることを前提にするべきである。今の late intercept が env shadow で state を表現しているなら、call-site direct execution の前に state storage を frame 化するか、少なくとも frame 化へ移行できる compatibility layer を置く必要がある。

---

## 3. 次に導入すべき IR / runtime 表現

### 推奨する分割

名前としては、`DirectStateGet` / `DirectStateSet` だけをいきなりトップレベルに増やすより、概念上は `KnownOperationCall` を置き、その最初の variant として state を持つのがよい。

```rust
enum EvidenceVmOperationExecutionPlan {
    DirectAbortive,
    DirectTailResumptive,
    YieldFallback,
    BlockedFallback,
    GenericFallback,

    KnownOperationCall(KnownOperationExecutionPlan),
}

enum KnownOperationExecutionPlan {
    StateGet {
        plan_id: EvidenceVmKnownHandlerPlanId,
        handler_id: u32,
        allowed_set_id: EvidenceVmAllowedSetId,
        route: KnownOperationRoute,
    },
    StateSet {
        plan_id: EvidenceVmKnownHandlerPlanId,
        handler_id: u32,
        allowed_set_id: EvidenceVmAllowedSetId,
        route: KnownOperationRoute,
    },
}

enum KnownOperationRoute {
    StaticAllowedSet,
    ProviderGrant,
}
```

Rust の実装上は最初から enum nesting にしなくてもよい。次のように flat variant でもよい。

```rust
enum EvidenceVmOperationExecutionPlan {
    DirectStateGet {
        plan_id: EvidenceVmKnownHandlerPlanId,
        handler_id: u32,
        allowed_set_id: EvidenceVmAllowedSetId,
    },
    DirectStateSet {
        plan_id: EvidenceVmKnownHandlerPlanId,
        handler_id: u32,
        allowed_set_id: EvidenceVmAllowedSetId,
    },

    DirectAbortive,
    DirectTailResumptive,
    YieldFallback,
    BlockedFallback,
    GenericFallback,
}
```

ただし design note / naming では `KnownOperationCall` と呼んでおくと、あとで reader/accumulator/checked user handler へ拡張する時に「state だけの特殊処理」になりにくい。

### runtime frame

call-site direct state op に必須なのは runtime state frame である。

```rust
enum RuntimeKnownHandlerFrame {
    State(RuntimeStateHandlerFrame),
}

struct RuntimeStateHandlerFrame {
    plan_id: EvidenceVmKnownHandlerPlanId,
    handler_id: u32,
    state_def: DefId,
    state: Value,
    continuation: EvidenceVmKnownStateContinuationSemantics,
}
```

lookup は source name や path string ではなく、少なくとも次の identity の積で行う。

```text
plan_id
handler_id / capability id
operation role: get | set
allowed_set_id / provider grant permission
active frame identity
```

operation path は debug surface には残してよいが、direct execution の判定主因にしない方がよい。内部的に family path しかない段階でも、plan construction の時点で handler object id / allowed set / known state plan と結び、runtime hot path は id lookup へ寄せるべきである。

### frame entry / exit

`catch` が known state handler である場合、catch body 評価中に state frame を active stack へ push する。

```text
enter known state catch:
  initial state value を評価済みとして frame.state に入れる
  active_known_handler_frames.push(StateFrame)
  eval body
  pop frame
```

late catch-boundary intercept は、この frame から state を読む実装へ置き換えられる。これを先にやると、route-specific direct op 導入時の semantic delta が小さくなる。

---

## 4. proof はどこに置くべきか

proof は 1 箇所に押し込めず、4 層に分けるのがよい。

### 4.1 lowering certificate

ここは「producer の主張」を置く場所である。

```text
compiler-generated local mutable var lowering produced a known state handler
```

持つべき情報は、source path ではなく stable identity である。

```rust
struct LoweringStateHandlerCertificate {
    synthetic_var: SyntheticLocalVarId,
    family: EffectFamilyId,
    get_op: OperationId,
    set_op: OperationId,
    handler_expr: ExprId,
    state_def: DefId,
}
```

この certificate は「この handler が state handler である可能性が高い」という入口であり、最終 proof ではない。

### 4.2 specialize / runtime evidence surface

ここは route と identity の流通面である。

```text
operation call expr
  -> effect family / operation id
  -> evidence slot
  -> handler capability / allowed set candidate
  -> known handler plan candidate
```

ここでやるべきことは、`std.control.var.ref` などの string を復元することではない。call site と handler/capability/operation identity を失わず Evidence VM へ渡すことである。

### 4.3 Evidence VM plan

ここが最終的な static intersection を作る場所である。

```text
if
  operation call route proves handler H is visible
  H belongs to KnownHandlerPlan::State P
  operation role is P.get or P.set
  route is not blocked/delayed in a way direct op cannot preserve
then
  operation.execution = DirectStateGet/Set { P, H, visibility }
else
  keep existing execution
```

`EvidenceVmOperationObjectPlan` に `execution` が既にあるなら、そこに state direct variants を入れるのが自然である。`candidate_handler` と `visibility` も既にあるので、new plan は既存の direct route proof と known handler certificate の join になる。

### 4.4 runtime guard

runtime guard は proof の代替ではなく、stale/dynamic condition の確認である。

```text
- active state frame with plan_id exists
- active frame handler_id matches allowed handler/capability
- provider grant permission, if used, is still visible under current hygiene baseline
- no marker/provider/handler shadow invalidates the route
- operation payload shape matches get/set arity
```

guard failure は原則 fallback へ落とす。最初は fallback path を残し、counter を増やして、実運用で 0 になることを見てからより強い invariant にしてもよい。

---

## 5. marker / provider hygiene の守り方

route-specific direct state op で一番危ないのは、`get` / `set` が「同じ名前の近い handler」を勝手に掴むことである。これは絶対に避ける。

守るべき invariant は次である。

```text
Direct state op may only access the active state frame that corresponds
to the same handler object/capability proved visible for this operation call.
```

具体的には、plan construction で次を済ませる。

```text
operation object:
  slot_id
  candidate_handler
  visibility.allowed_set_id
  execution = DirectStateGet/Set { plan_id, handler_id, allowed_set_id }
```

runtime では次を見る。

```text
active_known_handler_frames.rev().find(|frame|
  frame.plan_id == plan_id
  && frame.handler_id == handler_id
  && route_visibility_is_still_valid(visibility)
)
```

`request_path == handler.get_path` のような path equality は、移行期の lookup では許容できても、最終 direct path の主判定にしない方がよい。path は `handler_id` や `operation_id` を得るための plan-time material であり、runtime hot path では id に落とす。

### provider grant route

provider grant を許す場合は、既存の `EvidenceProviderGrant` の hygiene baseline を使うべきである。新しい「marker stack が空なら OK」という dynamic shortcut を増やすのは避ける。今回の failed trial 2 が示す通り、この条件は hot path に当たらない上に、当たっても semantics の説明が弱い。

provider grant route は次のような扱いがよい。

```text
clean provider grant:
  DirectStateGet/Set allowed

dirty provider grant:
  fallback to generic request route
  counter increments:
    known_state_direct_route_reject_provider_dirty_add_id
    known_state_direct_route_reject_provider_dirty_handler
    known_state_direct_route_reject_provider_dirty_scope
```

ここでいう dirty は「direct route の proof が current dynamic scope に対して再利用不能」という意味であり、generic semantics が間違っているという意味ではない。

### blocked / delayed / callback boundary

blocked route、delayed boundary、callback boundary は direct state op の reject reason として明示する。

```text
Known state certificate exists
  but route is blocked       -> no direct op
  but delayed boundary exists -> no direct op initially
  but callback boundary exists -> no direct op initially
```

あとで explicit evidence carrying ができた provider env 経由の direct op を許すとしても、最初は conservative でよい。local mutable ref の hot path は、まず clean direct/static route で拾えるはずである。

---

## 6. continuation capture / multi-shot resume と state frame

direct state op は generic catch recursion を通らないので、state handler の意味を runtime frame 側で再現する必要がある。

基本意味論は次である。

```text
state frame is part of the dynamic continuation
capturing a continuation captures state frame snapshots
resuming a continuation forks those snapshots
```

`set` は raw shared cell mutation ではない。現在実行中の branch の state frame を更新するだけである。

```text
capture at x = 10

resume k():
  branch A frame starts with x = 10
  set x = 20

resume k():
  branch B frame starts with x = 10
```

もし同じ `Rc<RefCell<Value>>` を continuation 間で共有すると、branch A の `set` が branch B に漏れる。これは algebraic state handler の recursion semantics と違う。したがって、`RuntimeStateHandlerFrame` は continuation snapshot/fork に参加する必要がある。

### 実装上の段階

いきなり最適な one-shot destructive update を入れない方がよい。最初は常に snapshot/fork semantics を守る。

```text
StoredContinuation:
  frames: ...
  active_known_handler_frames_snapshot: Vec<RuntimeKnownHandlerFrameSnapshot>
```

resume 時:

```text
if multi-shot or unknown:
  clone/fork state frame values
else:
  later optimization may move/reuse
```

ここで Value が persistent/shared なら clone cost は大きくないはずである。大きい場合でも、それは `one-shot` proof を入れる後続 stage の問題であり、最初に raw cell semantics へ逃げる理由にはならない。

### direct op 自身は continuation を捕まえない

`get` / `set` は「現在の continuation に値を返す」だけである。generic request では operation が request を投げ、catch が continuation を resume する。direct state op では、それを局所的に次へ変換する。

```text
generic:
  request(get, k)
  catch handles get
  resume k(state)

direct:
  return state to current continuation
```

この変換が正しいのは、state handler certificate が「arm は tail-resume exactly once」と証明しているからである。ここが arbitrary handler へ一般化できない理由でもある。

---

## 7. `RefSet` を直接最適化してよいか

条件付きで yes である。ただし、route-specific direct state op より後にした方がよい。

### safe な形

`RefSet` 最適化は「local variable の syntax」を見るのではなく、reference expression が返す ref target に certificate を持たせる。

```rust
enum RuntimeRefRepr {
    Generic(Value),
    StateSlot(StateRef),
    Projection(ProjectionRef), // later
}

struct StateRef {
    plan_id: EvidenceVmKnownHandlerPlanId,
    handler_id: u32,
    slot: StateSlotId,
    permission: StateRefPermission,
}
```

`&x = value` のような assignment は、reference expression が `StateRef` を返し、active frame が一致し、hygiene proof が有効な時だけ direct set になる。

```text
eval reference
eval assigned value
if reference is StateRef and active frame matches:
  frame.state = assigned
  return ()
else:
  current RefSet protocol
```

これなら public `std.control.var.ref` は通常の abstraction のままである。generic code へ渡された user refs、file refs、projected refs、record-shaped refs は certificate がない限り generic protocol に残る。

### 先にやらない方がよい理由

今すぐ `RefSet` だけを direct 化すると、`known_state_direct_gets/sets` と `ref_set_*` の層が混ざり、どこで速くなったのか読みにくくなる。また、`r.update(f)` の評価順序や projection semantics へ踏み込みやすい。

順番はこうしたい。

```text
1. state frame storage
2. route-specific DirectStateGet/Set
3. certified RefSet direct assignment to StateRef
4. escaped StateRef receiver get/set
5. StateRef update(f)
6. ProjectionRef / lens plan
```

### `RefSet` direct assignment の評価順序

`RefSet` shortcut は、現在の評価順序を変えないことが重要である。現行 runtime は reference を先に評価している。direct path でも同じにする。

```text
reference_result = eval(reference)
assigned_result  = eval(value)
then write
```

`value` の評価中に effect が起きた場合、state write はまだ起きていない。`value` が abort/unhandled した場合も write は起きない。これは `r.update(f)` の後続 stage でも同じ原則になる。

### `r.update(f)` は別 stage

`r.update(f)` は assignment より難しい。正しい順序は次である。

```text
old = read state
new = evaluate f(old) in same dynamic context
write state only after f returns normally
return result / unit according to protocol
```

`f(old)` が continuation を capture したり、別 effect を投げたり、multi-shot resume されたりする場合がある。したがって、`update(f)` は direct state get/set が安定し、continuation canary が揃ってからでよい。

---

## 8. escaped `&x` をどう速くするか

escaped `&x` を fast にするには、heap cell 化ではなく **capability token 化** するのがよい。

```text
&x evaluates to StateRef(plan_id, handler_id, slot, scope_epoch)
```

この token は state の実体を持たない。active dynamic state frame への参照権だけを持つ。使う時に active frame を解決する。

```text
StateRef.get:
  find active frame matching plan_id/handler_id/scope
  if found and visible:
    return frame.state
  else:
    fallback/error matching generic behavior

StateRef.set:
  same lookup
  update frame.state
```

こうすると、`&x` を関数に渡しても、同じ dynamic extent 内なら fast path が取れる。一方、`&x` が scope 外へ escape して使われた場合、存在しない frame を勝手に heap cell として生かさない。これは現在の generic semantics に合わせて fallback か unhandled/runtime error にする。

### projected refs

`&record.field` や lens/projection は、`StateRef` へ直接混ぜない方がよい。

```rust
enum RefRepr {
    StateSlot(StateRef),
    Projection {
        base: Box<RefRepr>,
        projection: ProjectionPlan,
    },
    Generic(Value),
}
```

projection update は「base を read」「projection を update」「base を write」という focused update であり、state slot update より評価順序が複雑である。これを最初の stage に混ぜると canary が爆発する。

---

## 9. option 評価

### 1. Route-specific direct state op execution

最優先である。

理由:

```text
- 現在の direct execution が late すぎる問題を直接解く
- direct_effect_calls を増やせる
- operation object の generic-fallback を減らせる
- KnownHandlerPlan::State を本当に operation dispatch へ接続する
- 後続の RefSet shortcut の土台になる
```

注意点:

```text
- state storage を RuntimeStateHandlerFrame に寄せる必要がある
- marker/provider hygiene を allowed_set / handler_id で守る必要がある
- fallback counters を先に作る
```

期待値:

```text
50ms -> 20-35ms 程度の改善はあり得る
ただし RefSet protocol が残るため、これだけで 6ms 近辺までは行かない可能性が高い
```

### 2. General known-handler frame execution

概念としては正しいが、次の実装単位としては大きすぎる。

よい切り方は次である。

```text
general framework:
  KnownOperationCall
  RuntimeKnownHandlerFrame
  KnownHandlerCertificate

first instance:
  StateGet / StateSet only
```

つまり「一般 known-handler frame execution を設計語彙として採用し、実装は state に閉じる」のがよい。任意 handler operation を今から直接実行するのは危険である。同じ型と row を持つ handler でも、log、ignore、duplicate resume、forward、escape があり得る。handler meaning certificate なしには最適化できない。

### 3. Ref protocol optimization

期待 performance gain は高い。だが route-specific state op の後に置くべきである。

`RefSet` の 400 回はかなり怪しい。`known_state_direct_gets: 800` / `known_state_direct_sets: 400` という数から、1 assignment が少なくとも 2 get + 1 set 的な層を通っている。`ref_set_update_effect_calls: 400` と `ref_set_assignment_ref_update_requests: 400` も、local assignment にしては重い。

ただし、ここを直接触るなら次の命名にするべきである。

```text
bad:
  direct local variable assignment

good:
  certified RefTargetPlan::StateSlot assignment
```

これなら local-variable-only special case ではない。将来は `ProjectionRef` や checked lens ref へ同じ枠で拡張できる。

### 4. Iterator / `for` IR

今は後回しでよい。

`for` without refs が 6ms、pure recursive loop が 1.5ms なら、iterator/std abstraction overhead は確かにある。しかし local-ref sum は 50ms であり、差分の主因は ref/state/effect protocol である。

推奨順:

```text
first:
  make ref sum approach no-ref for

then:
  decide whether direct iterator IR is worth it
```

direct iterator IR を入れるなら、`for` という std 名で見るのではなく、lowering が作る certified iterator/fold shape を `LoopPlan` として持たせるのがよい。

```rust
enum ControlLoopPlan {
    CountedRangeFor { iterator, item_def, body },
    ListFor { list, item_def, body },
    GenericIteratorFallback,
}
```

だがこれは state/ref plan のあとでよい。

### 5. List merge / builder optimization

今は main path ではない。`nondet` が similar `list_merge_calls` でも 10ms 程度である以上、`&xs.push` の 75ms を list merge だけで説明しない方がよい。

ただし後続としては、builder/fusion plan は有望である。

```text
ListBuilderFrame:
  push accumulates into mutable builder inside a certified scope
  finalization freezes into persistent list
```

これは `nondet.list` や `for + push` の両方へ効く可能性がある。だが state/ref が generic protocol を抜ける前に builder を入れると、どの層が改善したか読めなくなる。

### 6. More continuation / scope executor work

今の local-ref sum では優先度低めである。

過去の ScopePlan work が nondet を速くしたなら、それは重要な成果である。ただし今回の数字では nondet はすでに 10ms、local-ref sum は 50ms である。continuation machinery が完全に消えたわけではないが、今の hot path は `RefSet` protocol と request-free でない `get/set` がより怪しい。

次に continuation/scope executor を触るなら、先に direct state route counters を入れ、まだ以下が高い時に戻るべきである。

```text
continuation_appends
request_continuation_appends
request_continuation_append_blocked_by_*
resume_plan_* around state get/set
```

---

## 10. 推奨 staged plan

### Stage A: 計測と plan-only classification

挙動変更なし。

目的は、どの call site が direct state op にできるかを plan/debug に出すこと。

追加する plan counters:

```text
plan_known_state_operation_candidates
plan_known_state_get_candidates
plan_known_state_set_candidates
plan_known_state_operation_direct_plans
plan_known_state_operation_reject_no_known_handler
plan_known_state_operation_reject_unknown_operation_role
plan_known_state_operation_reject_blocked_route
plan_known_state_operation_reject_delayed_boundary
plan_known_state_operation_reject_missing_visibility
plan_known_state_operation_reject_provider_dirty
```

debug output 例:

```text
operation object:
  expr: ...
  path: ...
  execution: direct-state-get
  known_handler_plan: ...
  handler_id: ...
  visibility: allowed-set ...
```

rollback:

```text
execution variant を作っても runtime では無視し、GenericFallback のまま扱う
```

acceptance:

```text
loop_for_sum_ref_20_discard:
  plan_known_state_get_candidates == 800
  plan_known_state_set_candidates == 400
  direct plan reject が予想外に増えない

operation objects:
  certified get/set が generic-fallback から direct-state-* へ分類される
```

### Stage B: RuntimeStateHandlerFrame を導入し、late intercept を frame 経由に変える

ここが重要である。route-specific direct op の前に、state の実体を frame へ移す。

```rust
struct RuntimeStateHandlerFrame {
    plan_id: EvidenceVmKnownHandlerPlanId,
    handler_id: u32,
    state_def: DefId,
    state: Value,
}
```

known state catch entry で frame を push する。既存の late catch-boundary direct get/set は、env shadow ではなく frame read/write を使う。

追加 counters:

```text
known_state_frame_entries
known_state_frame_exits
known_state_frame_reads_late
known_state_frame_writes_late
known_state_frame_missing_late
known_state_frame_shadow_compat_fallbacks
```

rollback:

```text
feature gate で旧 env shadow late intercept へ戻す
```

acceptance:

```text
既存 canary が compare-control match
known_state_direct_gets/sets は維持
runtime は悪化しても小幅
```

この stage で性能が少し悪くなっても許容してよい。これは次の direct route のための semantic storage migration である。

### Stage C: continuation snapshot/fork canaries

DirectStateGet/Set を default enable する前に入れる。

追加 counters:

```text
known_state_frame_snapshots
known_state_frame_forks
known_state_frame_resume_reuses
known_state_frame_resume_clone_fallbacks
known_state_frame_multishot_forks
```

canary:

```text
capture after x = 10; resume twice; both branches start at 10
nondet around x update; branches do not share updates
closure captures &x; resumed frame maps StateRef to resumed frame
```

rollback:

```text
state frame direct execution gate off
known state catch intercept fallback
```

### Stage D: Route-specific DirectStateGet/Set execution

ここで初めて request-free operation execution を有効にする。

実行点は effect op application の直前/直後がよい。引数評価順序は既存 Apply と一致させる。

概念:

```text
eval callee / know callee is effect op
eval arg
if operation call has DirectStateGet/Set plan:
  execute state op against active RuntimeStateHandlerFrame
else:
  existing apply_value / request path
```

実装上は、arg 評価中に request が出る場合のために専用 frame を持つと安全である。

```rust
Frame::DirectKnownOperationArg {
    apply: ExprId,
    callee: ExprId,
    execution: KnownOperationExecutionPlan,
}
```

`get` の payload は unit に近いはずだが、既存 semantics が payload をどう扱うかに合わせる。payload を評価しない shortcut は不可である。payload evaluation は effect を起こし得る。

runtime counters:

```text
known_state_route_direct_gets
known_state_route_direct_sets
known_state_route_request_free_gets
known_state_route_request_free_sets
known_state_route_frame_hits
known_state_route_frame_misses
known_state_route_visibility_hits
known_state_route_visibility_misses
known_state_route_arg_request_fallbacks
known_state_route_generic_fallbacks
direct_effect_calls
```

acceptance:

```text
direct_effect_calls > 0
known_state_route_direct_gets == 800
known_state_route_direct_sets == 400
known_state_direct_gets/sets at late catch boundary decrease correspondingly
operation objects are no longer generic-fallback for these calls
compare-control match
```

expected result:

```text
loop_for_sum_ref_20_discard:
  50ms -> maybe 20-35ms
```

ここで 6ms にならなくても失敗ではない。`RefSet` protocol がまだ残る。

### Stage E: Certified RefSet direct assignment to StateRef

ここから `RefSet` protocol を短絡する。

plan/runtime representation:

```rust
enum RefTargetPlan {
    StateSlot {
        plan_id: EvidenceVmKnownHandlerPlanId,
        handler_id: u32,
        permission: StateRefPermission,
    },
    Generic,
}
```

runtime counters:

```text
ref_set_state_slot_candidates
ref_set_state_slot_direct_sets
ref_set_state_slot_frame_hits
ref_set_state_slot_frame_misses
ref_set_state_slot_visibility_misses
ref_set_state_slot_fallback_non_state_ref
ref_set_state_slot_fallback_escaped
ref_set_state_slot_fallback_projection
ref_set_state_slot_fallback_user_ref
ref_set_protocol_calls_saved
```

acceptance:

```text
loop_for_sum_ref_20_discard:
  ref_set_update_effect_calls drops toward 0 for certified local state refs
  ref_set_assignment_ref_update_requests drops toward 0
  user/file/projected refs remain generic
  compare-control match
```

expected result:

```text
loop_for_sum_ref_20_discard:
  likely close to no-ref for + arithmetic overhead
  target rough range: 8-15ms before iterator work
```

### Stage F: Escaped StateRef receiver get/set

`&x` を関数に渡した場合にも `StateRef` token から active frame を見つける。

counters:

```text
state_ref_receiver_get_candidates
state_ref_receiver_set_candidates
state_ref_receiver_direct_gets
state_ref_receiver_direct_sets
state_ref_receiver_fallback_no_active_frame
state_ref_receiver_fallback_hygiene
state_ref_receiver_fallback_generic_ref
```

rollback:

```text
StateRef token を Generic ref wrapper として扱い、既存 protocol に戻す
```

### Stage G: `StateRef.update(f)`

assignment より後である。

counters:

```text
state_ref_update_candidates
state_ref_update_direct
state_ref_update_fallback_arg_effect
state_ref_update_fallback_multishot
state_ref_update_write_after_normal_return
state_ref_update_aborted_without_write
```

canary:

```text
f throws effect before returning -> state unchanged
f captures continuation -> resumed branches see correct old/new state
f returns normally -> write happens once
```

### Stage H: Iterator / List builder

ここから先は state/ref の次である。

```text
IteratorLoopPlan:
  reduce std for overhead

ListBuilderPlan:
  reduce push/list merge overhead
```

両方とも source name ではなく lowering certificate / shape certificate から作る。

---

## 11. candidate ranking

| Candidate | Semantic risk | Expected gain | Size | Effect-semantics fit | Reusable framework value | Recommendation |
|---|---:|---:|---:|---:|---:|---|
| Plan-only `KnownOperationCall` classification | Low | None directly | Small | High | High | Do first |
| `RuntimeStateHandlerFrame` + snapshot/fork canaries | Medium | Enables next gains | Medium | Very high | Very high | Do before direct route |
| Route-specific `DirectStateGet/Set` | Medium | Medium | Medium | Very high | High | Main next optimization |
| Certified `RefSet` direct assignment to `StateRef` | Medium | High | Medium | High if certificate-based | High | Do after direct state ops |
| Escaped `StateRef` receiver get/set | Medium-high | Medium | Medium-large | High if active-frame checked | High | Later |
| `StateRef.update(f)` | High | Medium-high | Large | Medium-high | High | Later with canaries |
| Iterator / `for` IR | Medium | Medium | Medium-large | Orthogonal | Medium | Defer |
| List builder / fusion | Medium-high | Medium | Large | Orthogonal but useful | Medium | Defer |
| General known handler execution for arbitrary handlers | High | Uncertain | Very large | Risky without certificates | Very high eventually | Design only, not next implementation |
| More scope/continuation executor work | Medium | Low-medium for this case | Medium | High | Medium | Defer until counters demand it |

The practical implementation order is:

```text
A. plan-only KnownOperationCall classification
B. RuntimeStateHandlerFrame storage
C. snapshot/fork canaries
D. DirectStateGet/Set request-free call sites
E. RefTargetPlan::StateSlot direct RefSet assignment
F. escaped StateRef get/set
G. update(f)
H. iterator/list plans
```

---

## 12. smallest canaries before route-specific state ops

### Basic state

```text
single local:
  my $x = 0
  &x = 1
  x == 1

read after write:
  &x = x + 1
  &x = x + 1
  x == 2

two locals:
  x and y updated interleaved
  writes do not cross
```

### Shadowing / nested handlers

```text
outer x, inner x:
  inner get/set never touches outer while inner active

same operation names, different hygienic families:
  direct op does not collide by path/name
```

### Blocked / delayed / callback

```text
blocked route:
  plan may see known handler, runtime must not direct execute

delayed boundary:
  direct state route rejects until explicit evidence support exists

callback boundary:
  provider/hygiene boundary prevents accidental direct access
```

### Continuation / multi-shot

```text
capture before set, resume twice:
  both resumes see pre-set state

capture after set, resume twice:
  both resumes see post-set state

nondet around local update:
  branches do not share destructive updates

escaped StateRef in captured closure:
  on resume, token resolves to resumed frame, not original live frame
```

### Ref protocol boundary

```text
&x passed to generic r.get():
  generic behavior preserved until StateRef receiver stage

&x passed to r.update(f):
  generic behavior preserved until update stage

user ref:
  no StateSlot shortcut

file ref:
  no StateSlot shortcut

projected ref:
  no StateSlot shortcut until ProjectionPlan
```

### Evaluation order

```text
set argument effect:
  set payload evaluated before state write

assignment value aborts:
  state unchanged

update(f) later:
  write only after f returns normally
```

---

## 13. concrete counters to add

### Plan counters

```text
plan_known_operation_calls
plan_known_operation_state_get_candidates
plan_known_operation_state_set_candidates
plan_known_operation_state_direct_gets
plan_known_operation_state_direct_sets

plan_known_operation_reject_no_operation_object
plan_known_operation_reject_not_call
plan_known_operation_reject_no_visibility
plan_known_operation_reject_no_candidate_handler
plan_known_operation_reject_no_known_handler
plan_known_operation_reject_wrong_handler
plan_known_operation_reject_wrong_operation
plan_known_operation_reject_blocked
plan_known_operation_reject_delayed
plan_known_operation_reject_provider_dirty
```

### Runtime direct op counters

```text
known_state_route_direct_gets
known_state_route_direct_sets
known_state_route_request_free_gets
known_state_route_request_free_sets
known_state_route_frame_hits
known_state_route_frame_misses
known_state_route_visibility_hits
known_state_route_visibility_misses
known_state_route_fallback_generic
known_state_route_fallback_arg_request
known_state_route_fallback_payload_shape
```

### State frame counters

```text
known_state_frame_entries
known_state_frame_exits
known_state_frame_max_depth
known_state_frame_snapshots
known_state_frame_forks
known_state_frame_multishot_forks
known_state_frame_one_shot_reuses
known_state_frame_missing
```

### RefSet counters

```text
ref_set_state_slot_candidates
ref_set_state_slot_direct_sets
ref_set_state_slot_protocol_fallbacks
ref_set_state_slot_frame_hits
ref_set_state_slot_frame_misses
ref_set_state_slot_visibility_misses
ref_set_state_slot_escaped_fallbacks
ref_set_state_slot_projection_fallbacks
ref_set_state_slot_user_ref_fallbacks
ref_set_protocol_calls_saved
```

### Hygiene counters

```text
known_state_direct_reject_blocked_route
known_state_direct_reject_delayed_boundary
known_state_direct_reject_callback_boundary
known_state_direct_reject_provider_dirty_scope
known_state_direct_reject_provider_dirty_add_id
known_state_direct_reject_provider_dirty_handler
known_state_direct_reject_handler_shadowed
```

---

## 14. rollback points

Each stage should have an explicit off switch.

```text
YULANG_VM_KNOWN_STATE_FRAME=0
  use old late intercept representation

YULANG_VM_DIRECT_STATE_OPS=0
  classify plans but execute generic request path

YULANG_VM_STATE_REF_SET=0
  StateRef exists but RefSet uses protocol

YULANG_VM_STATE_REF_RECEIVER=0
  escaped StateRef receiver falls back

YULANG_VM_STATE_REF_UPDATE=0
  update(f) remains generic
```

For each switch, compare-control should still match. If a stage improves one benchmark but increases reject counters or breaks canaries, keep the representation and leave the execution gate off, like the previous ScopePlan executor experiments.

---

## 15. paths to explicitly avoid

Avoid these even if they look attractive.

### 15.1 catch-body provider env wrapping

This already failed for good reason. It changes available provider environment near catch body, but it does not alter the operation call site's execution plan. The hot operation still creates a generic request.

### 15.2 active-handler shortcut when marker stacks are empty

This is too dynamic and too weak as a semantic proof. It also missed the hot path in the trial. Use route/certificate/visibility intersection instead.

### 15.3 source path / std path / name matching

Do not use:

```text
std.control.var.ref
std.control.var.run
field named update_effect
operation path string ending in get/set
source variable name
benchmark path
```

These are debug hints, not proof.

### 15.4 direct local variable cell

Avoid:

```rust
LocalRefCell(Rc<RefCell<Value>>)
```

as the semantic storage. It violates snapshot/fork unless wrapped in a much more complex continuation-aware cell. The principled storage is state frame snapshot/fork.

### 15.5 arbitrary handler shape recognition

Do not infer that user handler is state-like from superficial shape. If user handlers are optimized later, require explicit annotation/certificate and run the same checker.

### 15.6 optimizing `RefSet` by recognizing syntax only

`&x = value` can be optimized only if `&x` lowers to a certified `StateRef`. Do not add a VM branch for local variable names.

### 15.7 `Any` fallback

Unknown route/shape/receiver should mean generic fallback, not `Any`. `Unknown` remains the inference unknown; `Any` remains top.

### 15.8 list builder first

`&xs.push` is tempting because 75ms is the slowest number, but it mixes list merge with local state and ref protocol. Do not hide the state/ref problem under a builder optimization.

---

## 16. Answers to the specific questions

### Q1. Most likely bottleneck behind 50ms local-ref sum?

`RefSet` protocol + generic request/catch/resume for `get` / `set` / `ref_update` is the likely bottleneck. Late direct state execution removes handler arm evaluation, but not request allocation or operation dispatch. The modest increase in `expr_evals` compared with the large runtime increase points at protocol/control overhead rather than pure expression evaluation.

### Q2. Is late catch-boundary direct execution enough?

No. It is a good first slice, but architecture-level speedup needs route-specific direct state opcodes or equivalent `KnownOperationCall` execution before generic request creation.

### Q3. What exact IR next?

Introduce both:

```text
RuntimeKnownHandlerFrame::State
EvidenceVmOperationExecutionPlan::DirectStateGet/DirectStateSet
```

Conceptually group the latter under `KnownOperationCall`.

Do not jump straight to arbitrary `KnownHandlerFrame` execution. Start with state-specific operations under a general known-operation umbrella.

### Q4. Where should proof live?

```text
lowering certificate:
  producer identity for compiler-generated local state

specialize/runtime evidence surface:
  carries operation/handler/capability identities

Evidence VM plan:
  intersects route proof with known-handler certificate

runtime guard:
  validates active frame and hygiene visibility
```

No single layer should own all proof.

### Q5. How to preserve marker/provider hygiene?

Use handler/capability/allowed-set/provider-grant identity, not names. Direct op is allowed only if the active state frame corresponds to the same handler proved visible for that operation call. Dirty provider grants and blocked/delayed routes fall back.

### Q6. How should continuation capture / multi-shot resume handle state frames?

State frames are part of continuation snapshots. Resume forks them. Direct state operations mutate only the current branch's frame. One-shot destructive reuse is a later optimization after one-shot proof.

If direct ops share raw cells across resumes, semantics change. Do not do that.

### Q7. Is it safe to optimize `RefSet` directly for certified local state refs?

Yes, if the target is `RefTargetPlan::StateSlot` / `StateRef`, not local-variable syntax. It is unsafe if implemented as a local-name special case or as a shortcut for any record that looks like a ref.

### Q8. How can escaped `&x` remain fast without turning all refs into VM cells?

Represent `&x` as a `StateRef` capability token pointing to a dynamic state frame identity. It resolves to an active frame when used. It does not own storage. Outside the dynamic extent, it falls back or errors according to existing generic behavior.

### Q9. Smallest canaries?

Minimum set:

```text
single get/set
two independent locals
shadowed locals
same op names in different hygienic families
blocked route direct rejection
delayed/callback direct rejection
capture after set, resume twice
nondet around state update
&x passed to generic get/update remains generic
user/file/projected refs remain generic
set value effect before write
```

### Q10. Which attractive path should be avoided?

The most dangerous attractive path is `LocalRefCell` / syntactic `&x` shortcut. It will be fast quickly, but it will fight algebraic effects, multi-shot continuation, projection, escaping refs, and hygiene. The second most dangerous is arbitrary handler shape recognition without explicit certificate. The third is provider-env wrapping around catch bodies; it adds complexity without changing the call-site dispatch path.

---

## 17. Expected end state

The desired final layering is:

```text
source/lowering:
  local mutable var becomes certified state handler + StateRef producer

evidence/specialize:
  operation calls carry route/capability identity

Evidence VM plan:
  known handler certificate + route proof -> KnownOperationCall

runtime:
  active RuntimeStateHandlerFrame stores state
  DirectStateGet/Set execute request-free
  StateRef assignment can write frame directly
  generic refs remain generic
  continuation snapshot/fork preserves state semantics
```

The near-term performance target should not be “local-ref sum equals pure recursion”. That conflates state/ref work with `for` overhead. A better target is:

```text
after DirectStateGet/Set:
  local-ref sum substantially below 50ms, direct_effect_calls > 0

after RefSet StateSlot direct assignment:
  local-ref sum near no-ref for, perhaps 8-15ms

after IteratorLoopPlan:
  no-ref for and ref for both move closer to pure recursion
```

The key is to make each stage remove one semantic layer and prove it with counters. That avoids dormant complexity and keeps the optimization reusable beyond local variables.
