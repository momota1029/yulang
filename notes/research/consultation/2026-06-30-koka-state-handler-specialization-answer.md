# ChatGPT Pro answer: Koka-style state handler specialization

## 結論

Koka-style の `StateHandlerFrame` specialization は、Yulang にとって viable であり、長期的には `LocalRefCell` より筋がよい。ただし、最初の実装で「任意の handler source shape を認識して state slot 化する」ところまで行くべきではない。

推奨する軸は次である。

```text
architecture:
  KnownHandlerPlan
    -> StateHandlerPlan
         -> Runtime StateHandlerFrame
         -> direct StateGet / StateSet

first producer:
  compiler-generated local var lowering certificate

not first producer:
  arbitrary user handler shape recognition
```

つまり、最初の最適化対象は「local variable」ではなく、**証明済みの state-like handler** である。ただし、その証明済み handler を最初に供給するのは compiler-generated `var.run` でよい。これなら、`LocalRefCell` のような変数専用表現に見える部分を、より一般的な known-handler compilation の一実装として閉じ込められる。

重要な分担は次である。

```text
type/evidence route:
  この operation call がどの handler / capability に届くかを証明する

handler-state certificate:
  その handler が get/set state algebra と等価であることを証明する

runtime state frame:
  証明済み handler の状態を continuation と一緒に snapshot/fork 可能な slot として持つ
```

型と evidence だけでは handler の意味は証明できない。同じ operation row と同じ型を持つ handler でも、`set` を無視する、`get` にログを挟む、continuation を二回呼ぶ、別 handler へ転送する、といった実装が可能である。したがって、type/evidence は routing の根拠、state handler 化は別の certificate / checker の根拠、と分けるのが安全である。

---

## 1. viability: Yulang で成立するか

成立する。むしろ Evidence VM の現在の方向とは相性がよい。

Yulang 側にはすでに次の材料がある。

- operation call を `Direct` / `Blocked` / `Unhandled` に分類する control evidence
- handler arm の resumptive / abortive 分類
- callback boundary / delayed boundary をまたぐと direct route を止める考え方
- handler capability / allowed set / provider slot で hygiene を守る方向
- tail-resumptive arm を VM plan に反映しようとする足場

`StateHandlerFrame` は、この延長に自然に載る。

現在の local mutable var の遅さは、意味上の state update が毎回次を通る点にある。

```text
record select
  -> update_effect closure
  -> ref_update operation
  -> var.get operation
  -> var.set operation
  -> catch/resume machinery
  -> handler recursion
```

`StateHandlerFrame` では、証明済み route の上でこれを次へ潰す。

```text
get: read frame.state
set: frame.state = value; return ()
```

これは downstream の出力 patch ではなく、原因側の runtime / IR change である。したがって、質問の制約に合う。

ただし、この最適化が正しい条件は強い。

```text
operation call が direct route で handler H に届く
H が state handler と証明済み
operation が H の state operation として認証済み
continuation capture 時に H の state slot を snapshot/fork する
blocked / unknown / generic receiver は必ず fallback
```

この条件を満たせば、現在の algebraic effect semantics を保ったまま hot path から generic request allocation と continuation tree walk を外せる。

---

## 2. `LocalRefCell` より principled か

`StateHandlerFrame` は principled になり得る。ただし、設計の置き方次第である。

### principled な置き方

```text
Local mutable var is compiled via a known state handler.
The runtime representation of that known state handler uses a state slot.
Escaped refs are views/capabilities into that state handler when valid.
```

この場合、最適化対象は「local variable」ではなく「state algebra を実装する known handler」である。`LocalRefCell` は独立した意味論ではなく、`StateHandlerFrame` の中の state slot / state ref representation になる。

### principled でない置き方

```text
my $x だけ VM が特別扱いする
&x だけ special cell になる
handler/evidence route は見ない
continuation capture は後から辻褄合わせ
```

これは `LocalRefCell` と同じ問題を別名にしただけである。短期には速いが、projected ref、escaped ref、nondet、multi-shot、file/user ref が絡むたびに special case が増える。

したがって、推奨は次である。

```text
short-term implementation:
  metadata-annotated compiler-generated var.run only

architecture name:
  KnownHandlerPlan::State

runtime mechanism:
  StateHandlerFrame + StateRef capability
```

「最初の producer が compiler-generated var.run である」ことと、「architecture が local variable special case である」ことは同じではない。前者は安全な導入順序、後者は避けたい設計である。

---

## 3. 最初に認識すべき handler shape

最初は **get/set の state handler だけ** でよい。さらに、任意の user handler ではなく、compiler lowering が certificate を付けた handler を checker が検証する形がよい。

### 最初の exact shape

概念的には次を認識する。

```text
run(state0, body) =
  catch body:
    get(), k -> run(state, k(state))
    set(new), k -> run(new, k(()))
```

ただし、Yulang の current lowering では arm が単純な `k(state)` ではなく、`run state: k state` のように handler recursion を明示する形になる。したがって、既存の `tail_resume_arg` 的な「arm body が直接 `k arg` か」だけでは不足する。

必要なのは次の認識である。

```text
state arm body is tail call to the same handler runner
  with next_state = state expression
  and next_body = continuation(resume_value)
```

### verifier が受け入れる条件

最初の checker はかなり狭くてよい。

```text
StateHandlerPlan candidate:
  source = CompilerGeneratedStateHandlerCertificate
  handler_expr = catch expression / runner instance
  state_param = exactly one state parameter
  body_param = exactly one computation parameter
  operations = exactly get and set for one hygienic effect family

get arm:
  no guard
  continuation binder exists
  continuation is used exactly once
  continuation does not escape
  no delayed boundary around continuation use
  tail expression is reenter_same_handler(state, k(state))

set arm:
  no guard
  operation payload is one value new
  continuation binder exists
  continuation is used exactly once
  continuation does not escape
  no delayed boundary around continuation use
  tail expression is reenter_same_handler(new, k(()))

allowed wrappers:
  alpha-renaming
  let binding that does not duplicate/escape continuation
  coercions
  marker frames that preserve current hygiene semantics

not allowed in stage 1:
  guards
  multiple continuation calls
  captured continuation values
  arbitrary user code before/after resume
  state finalizer depending on final state
  handler forwarding
  open-coded source path matching
```

この狭さは欠点ではない。最初に欲しい性能問題は local mutable ref であり、そこに必要な algebra は `get/set` だけである。

### `any operation family whose arms tail-resume with updated state` は後回し

一般化は後で可能である。例えば次のような internal model には拡張できる。

```text
operation op_i(payload_i):
  transition_i(payload_i, state) -> (resume_value_i, next_state)
  then reenter_same_handler(next_state, k(resume_value_i))
```

だが、これは「任意の handler の意味を推論する」問題に近づく。第一段階でやると program equivalence に踏み込む。最初は certificate 付き `get/set` に限定し、checker が証明できないものは generic fallback に落とすべきである。

---

## 4. std 名や source string matching なしで実装できるか

できる。ただし、型情報だけでは足りない。

必要な identity は次である。

```rust
struct StateHandlerCertificate {
    family: EffectFamilyId,
    get_op: OperationId,
    set_op: OperationId,
    handler: HandlerId,
    state_type: Type,
    source: StateHandlerCertificateSource,
}

enum StateHandlerCertificateSource {
    CompilerGeneratedLocalVar { synthetic_id: SyntheticLocalVarId },
    CheckedAnnotatedHandler { annotation_id: AnnotationId }, // later
}
```

ここで `EffectFamilyId` / `OperationId` / `HandlerId` は elaboration / mono / control lowering が持つ stable internal identity であり、`std.control.var.run` という文字列ではない。

役割分担は次である。

```text
Type / effect row:
  get/set の arity, result type, state type 整合性を確認する

Evidence route:
  operation call が direct に handler capability へ届くか確認する

Certificate checker:
  handler arm が state transition と等価な shape か確認する

Runtime allowed set:
  provider / marker / hygiene を破らない direct access か確認する
```

`Any` を fallback に使う必要はない。unknown な route、unknown な shape、unknown な receiver は、型を丸めずに generic effect protocol へ落とす。

---

## 5. Control IR / VM plan の形

`StateHandlerScope` / `StateOperationGet` / `StateOperationSet` を直接 IR node として持つ案はわかりやすい。一方で、将来 nondet、iterator、projection、logging などの known handler 最適化を入れるなら、上位に `KnownHandlerPlan` を置いた方が special case の増殖を抑えやすい。

推奨は二層である。

```rust
enum KnownHandlerPlan {
    State(StateHandlerPlan),
    // future:
    // Nondet(NondetHandlerPlan),
    // Reader(ReaderHandlerPlan),
    // Writer(WriterHandlerPlan),
}

struct StateHandlerPlan {
    plan_id: KnownHandlerPlanId,
    handler_expr: ExprId,
    family: EffectFamilyId,
    state_type: Type,
    get_op: OperationId,
    set_op: OperationId,
    source: StateHandlerSource,
    continuation_semantics: StateContinuationSemantics,
}

enum StateHandlerSource {
    CompilerCertificate(SyntheticLocalVarId),
    ShapeCheckedAnnotation(AnnotationId),
}

enum StateContinuationSemantics {
    SnapshotFork,
}
```

その上で、lowered execution IR には route-specific opcode を出してよい。

```rust
enum ControlExec {
    EnterStateHandler {
        plan: KnownHandlerPlanId,
        init: ExprId,
        body: ExprId,
    },
    StateGet {
        plan: KnownHandlerPlanId,
        op_expr: ExprId,
    },
    StateSet {
        plan: KnownHandlerPlanId,
        op_expr: ExprId,
        value: ExprId,
    },
    GenericEffectOp {
        op_expr: ExprId,
    },
}
```

VM object plan 側では、既存の operation object に次のような lowering を足すのが自然である。

```rust
enum EvidenceVmOperationExecutionPlan {
    DirectAbortive,
    DirectTailResumptive,
    DirectStateGet { state_plan: KnownHandlerPlanId },
    DirectStateSet { state_plan: KnownHandlerPlanId },
    YieldFallback,
    BlockedFallback,
    GenericFallback,
}
```

runtime frame は handler/evidence frame と統合するのがよい。

```rust
struct RuntimeStateHandlerFrame {
    handler_capability: HandlerCapabilityId,
    plan: KnownHandlerPlanId,
    state: Value,
    generation: StateFrameGeneration,
}
```

direct op は raw pointer で適当な cell を触るのではなく、operation object が保持する `handler_capability` / `allowed_set` / `plan_id` に対応する active frame を触る。これで handler hygiene / marker / provider semantics を弱めずに済む。

---

## 6. continuation capture / multi-shot resume

ここが semantic core である。

`StateHandlerFrame` の state は、heap にある共有 mutable cell ではなく、**dynamic continuation の一部** として扱う必要がある。現在の handler recursion では state は `run(state, continuation)` の引数として continuation path に乗っている。したがって、direct slot 化してもその性質を保つ必要がある。

推奨 semantics は **snapshot/fork** である。

### capture

continuation capture 時、captured continuation から到達可能な active state handler frame を snapshot する。

```rust
struct CapturedContinuation {
    frames: Vec<CapturedFrame>,
    evidence_env: CapturedEvidenceEnv,
    state_snapshots: Vec<CapturedStateFrame>,
}

struct CapturedStateFrame {
    logical_frame: LogicalStateFrameId,
    plan: KnownHandlerPlanId,
    capability: HandlerCapabilityId,
    state_value: Value,
}
```

最初は保守的に、active state handler frames を全部 snapshot してよい。capture は local loop hot path ではないため、単純さを優先できる。

### resume

multi-shot resume では、snapshot から fresh な state frames を作り、captured frames / env / escaped state refs の handle を fresh frames へ remap する。

```text
capture at x = 10
resume k ()  => branch A starts with x = 10
resume k ()  => branch B starts with x = 10
branch A writes x = 20
branch B still starts from x = 10
```

これは current handler recursion semantics に最も近い。raw shared cell semantics にすると、branch A の update が branch B へ漏れ、multi-shot handler / nondet で観測可能に変わる。これは不可である。

### one-shot optimization

one-shot が証明できる場合だけ destructive reuse してよい。

```text
semantic rule:
  snapshot/fork

optimization:
  if one-shot proven, reuse state frame without observable sharing
```

既定を shared cell にして、multi-shot のときだけ後付けで修正する方針は避けるべきである。バグが小さい canary を通り抜け、nondet と組み合わせたときに壊れやすい。

### remap 対象

resume 時の remap 対象は少なくとも次である。

```text
VM frames 内の state frame handles
closure env 内の state ref values
record / tuple / list 内に入った escaped state refs
handler evidence env 内の provider references
operation fast-path cache が持つ frame reference
```

fast path cache に raw frame index を持たせる場合、capture/resume 後に stale index を触らない仕組みが必要である。`generation` を持つ handle にするか、resume 時に必ず remap する。

---

## 7. escaped refs の扱い

`std.control.var.ref` は公開 abstraction として残す。内部表現だけを変える。

推奨する内部表現は次のような tagged ref である。

```rust
enum RefRepr {
    StateSlot(StateRef),
    Generic(Value),
    Projection(ProjectionRef), // later
}

struct StateRef {
    plan: KnownHandlerPlanId,
    capability: HandlerCapabilityId,
    logical_frame: LogicalStateFrameId,
    state_type: Type,
}
```

`&x` が generic code に渡る場合でも、型上は `std.control.var.ref` のままである。違いは receiver の runtime representation だけである。

### direct 化できるケース

```text
$x
  -> compiler-known StateGet

&x = v
  -> compiler-known StateSet

foo(&x) の中で r.get()
  -> receiver が StateSlot かつ active matching frame があれば receiver fast path
  -> それ以外は Generic(Value) protocol
```

最初の stage では `$x` と `&x = v` だけ direct 化し、generic `r.get()` receiver fast path は後回しでもよい。これだけでも catastrophic case の大部分を潰せる。

### escape out of scope

`&x` が `var.run` の dynamic extent の外へ出たとき、VM が heap cell として生かし続けてはいけない。現在の generic semantics では、handler scope 外で `get` / `set` を呼ぶと、その `var` effect は handler に届かない。StateRef でも同じ挙動を保つ必要がある。

したがって、StateRef の operation は次のように扱う。

```text
matching active state frame exists:
  direct read/write

matching active state frame does not exist:
  generic effect protocol へ fallback
  または current semantics と同じ unhandled effect / runtime error
```

どちらにするかは現在の generic VM の挙動に合わせる。少なくとも、scope 外で過去の state slot を勝手に保持して読めるようにしてはいけない。

### user / file / projected refs

user-defined refs、file refs、generic record refs は `Generic(Value)` のままにする。`get` / `update_effect` という field を持っているだけで StateRef に昇格してはいけない。

StateRef 化の根拠は次だけである。

```text
internal certificate + evidence route + active handler capability
```

source path、field name、benchmark 名、std function string は使わない。

---

## 8. `ref_update` と projected refs

`ref_update` は消さない。generic truth surface として残す。

現在の `ref.update(f)` の本質は次である。

```text
old = r.get()
new = f(old)
r.set(new)
```

ただし、実際には `update_effect()` と `ref_update` handler を経由することで、projection chain が focused update を実装できる。ここを雑に direct 化すると、評価順序や effect scope が変わる。

### stage 1

stage 1 は direct `get` / `set` だけに絞る。

```text
local assignment:
  &x = expr
  -> StateSet

local read:
  $x
  -> StateGet

r.update(f):
  generic protocol のまま
```

### stage 2/3

StateRef receiver の `r.update(f)` fast path を入れるなら、次を正確に守る。

```text
old = read state slot
new = evaluate f(old) in the same dynamic context
write state slot after f returns normally
```

`f` が effect を起こす場合、handler / marker / provider scope を飛ばしてはいけない。`f` が continuation を capture する場合、capture される state は `f` 評価時点の state でなければならない。ここが不安なら、`r.update(f)` はしばらく generic fallback でよい。

### projected refs

projection は別の known plan として後から入れるのがよい。

```rust
enum ProjectionPlan {
    RecordField(FieldId),
    TupleIndex(usize),
    ListIndexKnown(usize),
}
```

`ProjectionRef(base, lens_chain)` は次を実装する。

```text
projection.get:
  root = base.get()
  return lens_chain.get(root)

projection.set(v):
  base.update(root => lens_chain.set(root, v))

projection.update(f):
  base.update(root => {
    focus = lens_chain.get(root)
    new_focus = f(focus)
    lens_chain.set(root, new_focus)
  })
```

base が `StateSlot` なら direct update できる。base が `Generic` なら `ref_update` protocol へ fallback する。

ただし、これは stage 1 に入れない方がよい。まず state get/set と continuation snapshot/fork の semantic canary を固める。projection はその後で、純粋な structural lens に限って足す。

---

## 9. 実装 stage と rollback points

### Stage 0: counters / canaries / oracle

挙動変更なしで観測を増やす。

```text
counters:
  effect_request_allocations_by_family
  effect_route_direct_get
  effect_route_direct_set
  generic_ref_get_calls
  generic_ref_update_effect_calls
  ref_update_requests
  handler_frame_state_snapshots
  continuation_resume_forks
  blocked_state_fastpath_attempts
  state_fastpath_fallbacks
```

feature flag を最初から置く。

```text
YULANG_KNOWN_STATE_HANDLER=off|plan-only|direct-local|direct-ref|direct-projection
```

rollback point: flag off で完全に既存 generic path へ戻る。

### Stage 1: plan-only KnownHandlerPlan

control/evidence VM に `KnownHandlerPlan::State` を作るが、実行は変えない。

出力例:

```text
known handlers:
  h42 state family f17 get op3 set op4 source compiler-local-var
known operations:
  e81 state.get direct h42
  e88 state.set direct h42
fallbacks:
  e92 state.set blocked delayed_boundary
```

この時点で、既存実行結果と一致することを確認する。

rollback point: plan generation を無視する。

### Stage 2: direct `$x` / `&x = v` only

compiler-generated local var の direct get/set だけ実行に使う。escaped ref receiver はまだ generic でよい。

```text
EnterStateHandler(init, body)
StateGet(plan)
StateSet(plan, value)
```

operation route が `Direct` でない場合、必ず generic fallback に落とす。

rollback point: operation execution plan を `GenericFallback` に戻す。

### Stage 3: continuation snapshot/fork

StateHandlerFrame を continuation snapshot に含める。

multi-shot canary をここで増やす。ここを通すまでは、direct state handler を default にしない方がよい。

rollback point: direct state handler flag off。

### Stage 4: escaped StateRef receiver fast path

`&x` を `StateRef` として持ち運び、generic code の `r.get()` / simple set equivalent を receiver fast path に落とす。

ただし、matching active frame がない場合は current semantics と同じ fallback/error にする。

rollback point: StateRef receiver fast path だけ off。

### Stage 5: `r.update(f)` fast path

評価順序と continuation capture canary を固めた後で入れる。

rollback point: update fast path だけ off。

### Stage 6: structural projection / lens plan

record field / tuple index など、compiler-known structural projection だけ direct 化する。user-defined projection は generic のまま。

rollback point: projection fast path だけ off。

### Stage 7: user annotated state handlers

`#[state_handler]` 的な internal annotation を導入し、checker が shape を検証できた user handler だけ state plan にする。ここまで来て初めて、compiler-generated local var 以外へ一般化する。

rollback point: annotation producer off。

---

## 10. canaries

最低限、次の semantic canary が必要である。

### 基本 state

```text
single local var read/write
nested local vars with same operation family but different hygienic ids
shadowed local var
two independent locals updated interleaved
local var under nested handlers
```

### generic ref boundary

```text
pass &x to function that calls r.get()
pass &x to function that calls r.update(f)
store &x in record/tuple/list and use inside scope
return &x outside scope and call get/set: current generic behavior と一致
user-defined ref with same fields remains generic
file ref remains generic
```

### hygiene / marker / provider

```text
same operation path under different hygienic provider
operation crossing callback boundary falls back
operation crossing delayed lambda/thunk boundary falls back unless evidence env explicitly carries provider
nested state handlers with same op names do not capture each other
blocked route never performs direct StateGet/StateSet
```

### continuation / multi-shot

```text
capture after state update, resume twice: both start from captured value
branch A update does not leak to branch B
nondet around local state update produces same list as generic VM
continuation captured inside f of r.update(f) preserves old/new timing
escaped StateRef inside captured closure remaps to resumed frame
```

### `ref_update` order

```text
f in r.update(f) observes old state
state is written only after f returns normally
if f aborts/raises effect, write does not happen unless generic semantics did
projection update preserves root structure update order
```

### performance canaries

```text
for_no_ref remains in the same range
for_sum_ref drops from catastrophic path
nondet does not regress unexpectedly
request allocation count for local get/set goes near zero
state snapshot count is zero on plain loops
```

一番大事なのは、debug / CI で `known-state` と `generic` を比較できる oracle mode を短期間でも持つことだ。

```text
run generic VM
run known-state VM
compare observable result / diagnostics / unhandled effects
```

全プログラムで常時二重実行する必要はないが、canary suite では強い保険になる。

---

## 11. nondet にも効くか

少し効くが、主戦場は別である。

`StateHandlerFrame` は `get/set` state algebra を slot に落とす最適化である。nondet の `each/list` は、基本的に continuation capture / multi-shot resume / result accumulation の問題である。

known-handler compilation の枠組み自体は nondet にも有効である。

```text
known operation route
known handler capability
one-shot / multi-shot arm classification
request allocation削減
```

しかし、nondet を速くするには `StateHandlerFrame` ではなく、別の plan が必要である。

```rust
enum KnownHandlerPlan {
    State(StateHandlerPlan),
    Nondet(NondetHandlerPlan),
}
```

`NondetHandlerPlan` 側では次が主題になる。

```text
multi-shot continuation representation
resume cloning cost
result builder/list accumulation
branch scheduling
one-shot yield fast path
```

つまり、Koka-style evidence / known-handler route は共通基盤として効く。ただし state slot 化が nondet の本丸ではない。

---

## 12. std `for` は同じ機構か、別 IR か

短期では別 IR がよい。

現在の測定では、`for_no_ref` は pure recursion より遅いが catastrophic ではない。catastrophic な差は local mutable ref が generic effect protocol を通る点にある。したがって優先順位は次である。

```text
1. known state handler for local mutable ref
2. continuation snapshot/fork correctness
3. escaped ref fast path
4. direct iterator IR for std for
```

`for` は algebraic effect handler というより、iterator / loop lowering の問題である。将来は `KnownCallPlan::ForIn` や `IteratorLoopPlan` として evidence / specialization infrastructure に載せてもよい。ただし、`KnownHandlerPlan` に無理に押し込む必要はない。

```rust
enum KnownPlan {
    Handler(KnownHandlerPlan),
    Call(KnownCallPlan),
}

enum KnownCallPlan {
    ForInRange,
    ForInList,
    MapList,
}
```

こう分けると、handler optimization と iterator lowering の責務が混ざらない。

---

## 13. option ranking

### 実用順位

| rank | option | 評価 |
|---:|---|---|
| 1 | metadata-annotated compiler-generated `var.run` only | 最初に ship する対象として最良。semantic risk が低く、今回の catastrophic case に直接効く。ただし architecture 名は `KnownHandlerPlan::State` にする。 |
| 2 | Koka-style `StateHandlerFrame` | 長期 architecture として最良。local var だけでなく state-like handler へ広げる足場になる。snapshot/fork を正しく入れる必要がある。 |
| 3 | general known-handler plan derived from evidence routes | 将来の spine として重要。ただし evidence route だけでは handler semantics を証明できないため、certificate / checker と併用する。第一段階で過度に一般化しない。 |
| 4 | pure `LocalRefCell` | raw shared cell としては避けたい。`StateHandlerFrame` の state slot / `StateRef` representation としてなら採用可。architecture の主語にしない。 |
| 5 | direct iterator IR for `for` | 有用だが今回の 2 秒問題の主因ではない。state handler 後でよい。 |
| 6 | doing nothing short-term except counters/canaries | Stage 0 として必須。ただし、それだけで止まる価値は低い。 |

### criterion 別

| criterion | best-to-worst |
|---|---|
| semantic risk の低さ | counters/canaries → annotated `var.run` → direct iterator IR → StateHandlerFrame → pure LocalRefCell → fully general shape recognition |
| expected performance gain | StateHandlerFrame / annotated `var.run` / LocalRefCell → general known-handler → direct iterator IR → counters only |
| implementation size の小ささ | counters → annotated `var.run` plan-only → pure LocalRefCell → direct iterator IR → StateHandlerFrame with snapshot → general known-handler |
| algebraic-effect semantics との fit | general known-handler + certificate → StateHandlerFrame → annotated `var.run` → direct iterator IR → pure LocalRefCell |
| future special-case accumulation 回避 | KnownHandlerPlan spine → StateHandlerFrame → annotated producer → direct iterator IR as separate KnownCallPlan → pure LocalRefCell |

このランキングで大事なのは、`annotated var.run only` と `StateHandlerFrame` を対立させないことだ。

```text
ship unit:
  annotated compiler-generated var.run

semantic architecture:
  Koka-style known state handler

runtime representation:
  StateHandlerFrame / StateRef
```

この組み合わせが一番バランスがよい。

---

## 14. 避けるべき attractive-looking approaches

### 1. std path / source string matching

`std.control.var.run` や `var_ref` という文字列を見て fast path に入る案は避ける。std 実装の変更、rename、re-export、user-defined lookalike で壊れる。

### 2. record field shape matching

`get` と `update_effect` field を持つ record を ref とみなす案も避ける。user ref / file ref / custom ref が巻き込まれる。

### 3. 任意 handler の syntactic equivalence checker

最初から arbitrary handler を source shape で認識しようとすると、すぐに program equivalence 問題になる。annotation / certificate なしの一般認識は diagnostic だけに留めるべきである。

### 4. raw shared `Rc<RefCell<Value>>`

multi-shot continuation で state sharing が漏れる。one-shot 専用最適化として証明後に使うのはありだが、semantic default にしてはいけない。

### 5. continuation capture を後回しにした direct state

plain loop benchmark は通るが、nondet / capture で壊れる。direct state を default にする前に snapshot/fork canary を入れる。

### 6. `ref_update` を local assignment と同一視する

`ref_update` は projection protocol でもある。local `set` は direct 化してよいが、`r.update(f)` と projection は評価順序と effect scope が絡むため後段に分ける。

### 7. blocked route の speculative direct access

「たぶん同じ handler だから」と delayed/callback boundary 越しに direct frame を触るのは不可。Evidence VM の hygiene の価値を壊す。

### 8. `Any` fallback

unknown shape を `Any` で丸めて進める必要はない。`Any`, `Never`, `Unknown` を混ぜず、unknown は generic fallback に落とす。

### 9. output-level patching

runtime_execute の結果や downstream codegen だけで local ref を潰すと、handler semantics の根拠が消える。control IR / VM plan で cause-side に入れるべきである。

---

## 15. 最終提案

最終的な設計名はこれがよい。

```text
KnownHandlerPlan::State
RuntimeStateHandlerFrame
StateRef capability
StateGet / StateSet execution plan
SnapshotFork continuation semantics
```

最初に実装する producer はこれでよい。

```text
CompilerGeneratedLocalVarStateCertificate
```

最初に direct 化する operation はこれだけでよい。

```text
local read  -> StateGet
local write -> StateSet
```

generic `std.control.var.ref` は残す。

```text
public abstraction:
  ref { get, update_effect, update }

internal fast path:
  StateRef receiver if certified and active

fallback:
  generic protocol
```

この設計なら、前回の `LocalRefCell` plan で必要だった実装上の cell / snapshot / fork の知見を捨てずに、それを Koka-style evidence passing / known-handler compilation の中へ移せる。

言い換えると、採るべき答えは「`LocalRefCell` か `StateHandlerFrame` か」ではなく、次である。

```text
Use StateHandlerFrame as the semantic optimization.
Use a cell-like state slot as its runtime representation.
Let compiler-generated local var be the first certified instance.
Keep all uncertified refs and handlers on the generic effect protocol.
```

これが、性能・意味論・将来の special-case 抑制のバランスが最もよい。
