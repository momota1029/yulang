結論から言うと、`apply_scoped_value_result` は「速くするために迂回したい補助関数」じゃなくて、**call boundary を open して、結果に対して hygiene を close する意味論上の primitive** として扱った方がいいねぇ。

今回壊れたのは、continuation call shortcut が悪いというより、shortcut 側が **「scoped function-call marker を閉じた」という証明を持たずに request-free route へ直行した** のが本体だと思うよ〜。

## 0. 現状の読み

今の Evidence VM では、`apply_scoped_value_result` が active marker plan から `function_call_markers` を作って、callee の形に応じて「callee へ marker を合成」「結果を close」「marker frame を張って apply」のどれかを選んでいる。つまりここは単なる wrapper じゃなく、関数呼び出し固有の marker transform と close 点になっているねぇ。

さらに `with_marker_frame` は、active frame / handler frame / add-id / marker plan の長さを snapshot してから body を走らせ、出てきた `Value` / `GenericRequest` / `RoutedYield` / `DirectTailResumptive` へ close 処理をかけている。ここで `handler_boundary` も計算しているから、ここを飛ばすと callback marker が閉じないだけじゃなく、**handler 可視性の証拠**も落ちる。

過去メモでも、`apply_scoped_value_result` を飛ばして EffectOp を直接 force する案は一時的に速く見えたが、function-call marker を省いて hygiene の根拠がなくなるので採られていない。これは今回の regression と同じ根っこだねぇ。

---

## 1. scoped apply / marker closure は evidence-passing runtime でどう表すか

私は `MarkerFrame` ではなく、IR 上に **`CallBoundary` / `HygieneBoundary`** を立てるのがよさそうだと思うよ〜。

今の VM の構造を evidence-passing へ移すなら、こんな抽象が要る。

```rust
struct EvidenceCallBoundary {
    call_site: ExprId,

    // active_marker_plan を function-call 用に変換したもの
    call_hygiene: HygienePlanId,

    // call によって渡される positive provider evidence
    provider_env_delta: EvidenceEnvDeltaId,

    // provider grant が作られた時点の negative/hygiene gate
    route_scope: EvidenceRouteScope,

    // fallback VM へ戻るときの marker/request bridge
    fallback_bridge: HygieneToRequestBridgeId,
}

enum EvidenceResult {
    Value(ValueId),
    DirectAbortive(DirectAbortiveSignal),
    DirectTailResumptive(DirectTailSignal),
    Yield(EvidenceYield),
    FallbackRequest(EvidenceRequest),
}
```

大事なのは `enter` より **`close(result)`** だねぇ。

```text
run under EvidenceCallBoundary
  result = eval call body

close(result):
  Value(v)
    -> v に call_hygiene を付ける
       ただし value wrapper ではなく object/evidence graph 側へ付けてもよい

  DirectTailResumptive(sig)
    -> payload を close
    -> resumption に resume_hygiene を付ける
    -> handler_boundary を記録する

  Yield(sig)
    -> payload / continuation / handler visibility を close
    -> request fallback へ変換可能な形にする

  FallbackRequest(req)
    -> payload を close
    -> continuation に resume_hygiene を付ける
    -> guard_ids / carried_guards / handler_boundary を埋める

  DirectAbortive(sig)
    -> 「本当に close 不要」という証明がある場合だけ素通し
       それ以外は DirectAbortiveClosed か fallback へ落とす
```

今の `close_marker_frame_signal` は、`DirectTailResumptive` と `RoutedYield` と `GenericRequest` には marker close / resume plan / handler boundary を入れている。一方で `DirectAbortive` はそのまま通している。これは現 VM の計算規則としては分かるけど、evidence IR では **DirectAbortive がなぜ close 不要なのか**を execution class の証明として持たせた方が安全だねぇ。

つまり、continuation call shortcut 側のルールはこれだと思う。

```text
shortcut may bypass apply_scoped_value_result
only if it carries an equivalent EvidenceCallBoundary::close proof
```

言い換えると、shortcut は `apply_scoped_value_result` を消していいんじゃなくて、**`apply_scoped_value_result` の close 結果を IR 上で先に持つ**必要がある。

---

## 2. marker を値 wrapper ではなく provider/evidence/object graph 側へ移せるか

可能だよ〜。ただし「marker を値から消す」ではなく、**marker の意味を routing evidence へ移す**という形になる。

今の runtime value は `Marked { value, markers }` を持っていて、closure / effect op / continuation / thunk / adapter など higher-order な値だけ hygiene が観測される構造になっている。 さらに closure や thunk はすでに `provider_env` を持っているから、value wrapper から object graph へ寄せる下地はある。

ただし、全部を lexical provider env に混ぜるのは危ないねぇ。provider grant は「その call/action activation の間だけ渡された契約 capability」で、closure 作成時の lexical evidence とは寿命も根拠も違う。メモでも `lexical evidence` と `contract-passed evidence` を分ける案が出ていて、ここはかなり筋がいい。

私なら object graph はこう分ける。

```rust
struct ClosureObject {
    code: FunctionId,
    env: ValueEnvId,
    lexical_evidence: EvidenceEnvId,
}

struct ThunkObject {
    body: ExprId,
    env: ValueEnvId,
    lexical_evidence: EvidenceEnvId,
}

struct ContinuationObject {
    segments: ContinuationSegmentId,
    perform_evidence: EvidenceEnvId,
    resume_policy: ResumeRoutingPolicyId,
}

struct FunctionAdapterObject {
    function: ValueId,
    adapter: EvidenceAdapterId,
    lexical_evidence: EvidenceEnvId,
}

struct ProvidedValue {
    value: ValueId,
    provider_env: EvidenceEnvId,
    grant_scope: ProviderGrantScopeId,
    contract: EffectContractId,
}
```

そして marker 相当はここへ行く。

```rust
struct RoutingPolicy {
    guard_own_path: bool,
    guard_foreign_path: bool,
    preserve_own_on_resume: bool,
    carry_after_frame: bool,
    blocker: VisibilityBlockerId,
}

struct HandlerEvidence {
    id: HandlerEvidenceId,
    handled_slot: EvidenceSlotId,
    handler_expr: ExprId,
    arm_table: ArmTableId,
    definition_env: EvidenceEnvId,
    routing_policy: RoutingPolicyId,
    prompt_or_guard: GuardId,
}
```

これは Yulang の設計メモとも合う。handler-passing runtime では、現在の marker frame / add-id / guard / carried guard が **evidence routing wrapper** になる、という整理がすでに書かれている。

ただし、値 wrapper をなくしても **projection propagation** は消せない。record/list/tuple/data constructor から closure/thunk/continuation が取り出された瞬間に hygiene が必要になるから、pure data の marker は遅延できても、field select / pattern bind / list item projection の境界は残る。これは既存メモでも危険点として明示されている。

なので方針はこうだねぇ。

```text
pure scalar / closed pure data:
  marker なしでよい

higher-order object:
  lexical_evidence を持つ

call/action/returned thunk:
  ProvidedValue / ProviderGrant を持つ

projection:
  object graph 側の hygiene を子要素へ伝播

fallback bridge:
  object graph hygiene を現 VM の marker/request/guard へ変換
```

---

## 3. DirectAbortive / DirectTailResumptive が request を作らないための不変条件

ここはかなり明確に線を引いた方がいい。`request-free` は「request が不要」じゃなくて、**request が持っていた観測可能情報を別表現で全部持っている**という意味だねぇ。

### 共通条件

まず共通でこれ。

```text
A. handler identity が証明済み
B. operation path/family が証明済み
C. payload が call boundary close 済み
D. provider grant の scope がまだ有効
E. hygiene baseline 以後に shadowing がない、または shadowing を signal が保持している
F. continuation / resumption が MarkerFrame / ProviderEnv scope を保存している
G. fallback request へ同値変換できる
```

今の provider grant は `scope_id` と `hygiene_baseline` を持っていて、baseline は marker plan / active add-id / active handler frame の長さを記録している。これが provider route を request-free にする時の最低限の gate だねぇ。 Runtime 側でも provider route lookup は active provider env から grant を作り、scope と hygiene baseline を route origin に載せている。

### DirectAbortive

`DirectAbortive` は一番速くできるけど、一番雑に扱うと怖い。

request-free にしていい条件はこれ。

```text
DirectAbortive request-free invariant:

1. handler arm は continuation を実質的に使わない
2. operation は resume / yield / returned effect thunk を作らない
3. payload に必要な call hygiene は close 済み、または payload が pure
4. provider route 由来なら grant gate が通っている
5. callback-origin effect を inner handler が捕捉する余地がない
6. handler body が外へ返す higher-order value に必要な hygiene は別 boundary で閉じる
```

現行の `eval_direct_abortive_arm` でも、wild 以外の continuation binding を DirectAbortive では拒否している。これは DirectAbortive を request-free にする不変条件の一部として IR に上げた方がいいねぇ。

### DirectTailResumptive

`DirectTailResumptive` は request-free でも、実質的に request の hygiene 部分を持つ必要がある。

現行構造でも `EvidenceDirectTailResumptive` は `guard_ids` / `carried_guards` / `handler_boundary` / `continuation` を持てるようになっている。 `AddIdShadowed` の場合も、完全 fallback ではなく guarded direct-tail として request-like guard state を集めて `EvidenceDirectTailResumptive` に載せる実験が採られている。

不変条件はこうだねぇ。

```text
DirectTailResumptive request-free invariant:

1. handler identity が static direct か provider grant で証明済み
2. provider grant の scope / baseline gate が通る
3. AddIdShadowed は guard_ids / carried_guards として signal に反映済み
4. HandlerShadowed / ScopeMissing は request fallback
5. payload は call boundary close 済み
6. resumption は resume_hygiene / provider_env を復元する
7. continuation append は MarkerFrame / ProviderEnv の dynamic scope を越えて flatten しない
8. catch 側の visible predicate が GenericRequest と同じ結果になる
```

実際、現行の `force_effect_result` も DirectTail で `direct_tail_gate_failure` を見て、`AddIdShadowed` だけ guarded direct-tail にし、他は fallback に残している。 さらに catch 側では `visible_direct_tail_resumptive` が request と同じ可視性判定を使って、見えなければ `Unhandled` request へ戻している。

ここで continuation call shortcut の条件はかなり厳しい。

```text
Continuation call shortcut is valid only if:

- continuation object already contains closed call_hygiene, or
- active call_hygiene is empty, or
- shortcut creates an equivalent CallBoundary::close result
```

これを満たさない shortcut は、たとえ request を作らなくても hygiene 的には unsound だと思うよ〜。

---

## 4. Koka 的 evidence passing と Yulang の「契約した effect だけ捕捉する」衛生性

Koka 的な evidence passing は、ざっくり言うと **positive routing** が主役だねぇ。

```text
operation family -> evidence slot -> handler evidence -> handle / forward
```

Yulang はそこに **negative / hygiene routing** が同じ強さで乗る。

```text
operation family
+ contracted visibility
+ callback/projection blocker
+ provider grant provenance
+ resume policy
```

つまり Yulang の evidence slot は `family` だけでは足りない。

```rust
struct EvidenceSlotKey {
    family: PathId,

    // positive side
    demand_slot: SlotId,
    provider_slot: SlotId,

    // negative / hygiene side
    visibility_route: VisibilityRouteId,
    blocker_route: BlockerRouteId,

    // private tail / projection side
    projection_boundary: ProjectionBoundaryId,
}
```

Yulang の設計メモでも、handler/evidence-passing 方向は採るが、evidence は単なる handler pointer ではなく、positive evidence / negative hygiene evidence / private projection evidence を表す必要がある、と整理されている。

接続規則はこう書けると思う。

```text
perform(op, payload, slot, env):
  let route = env.lookup(slot)

  if route is PositiveHandler
     and hygiene_policy_allows(route, op.provenance, current_boundary):
       call handler evidence directly

  else if route has parent/outer evidence:
       yield/forward with continuation fragment

  else:
       FallbackToVm(op, payload, evidence_to_marker_bridge)
```

Koka の yield bubbling 相当は、Yulang では単なる outer handler search じゃなくて、**contract を持つ evidence object だけへ forward する**という制限付きになる。メモにも、callback-derived effect が unrelated inner handler に捕捉されてはいけない、これは late marker patch ではなく evidence routing で表すべき、とある。

なので `FunctionAdapterHygiene` は evidence runtime ではこうなる。

```rust
struct EvidenceAdapter {
    body_transform: EvidenceEnvTransformId,
    arg_transform: EvidenceEnvTransformId,
    return_transform: EvidenceEnvTransformId,

    // callback-origin effect を隠す blocker
    callback_blocker: VisibilityBlockerId,
}
```

Stage 2 の callback evidence adapter が local escape より先に必要、という既存メモの判断はかなり正しいと思う。local escape ですら callback-origin `return` を誤捕捉すると壊れるからだねぇ。

---

## 5. native / inline lowering 前に固定したい runtime IR

ここはかなり強めに言うけど、**今の request / marker / resume model を native 化する前に、evidence IR を固定した方がいい**。既存メモにも、current control VM は oracle/fallback として残し、evidence-passing model ができる前に current request/marker/resume model を native-code すると間違った cost structure を固定すると書かれている。

固定したい最小 IR はこれ。

```rust
struct EvidenceFunction {
    value_params: Vec<ValueParam>,
    evidence_params: Vec<EvidenceSlotId>,
    body: EvidenceExpr,
}

enum EvidenceExpr {
    Value(ValueId),

    Call {
        callee: ValueId,
        arg: ValueId,
        evidence_args: EvidenceEnvId,
        boundary: EvidenceCallBoundaryId,
    },

    Perform {
        family: PathId,
        payload: ValueId,
        slot: EvidenceSlotId,
        mode: OperationMode, // Abortive / OneShot / TailResumptive / MultiShot
    },

    Handle {
        body: Box<EvidenceExpr>,
        handler: HandlerEvidenceId,
        parent_env: EvidenceEnvId,
    },

    MakeClosure {
        code: FunctionId,
        env: ValueEnvId,
        lexical_evidence: EvidenceEnvId,
    },

    MakeThunk {
        body: ExprId,
        env: ValueEnvId,
        lexical_evidence: EvidenceEnvId,
    },

    Force {
        thunk: ValueId,
        boundary: EvidenceForceBoundaryId,
    },

    Resume {
        resumption: ResumptionId,
        arg: ValueId,
        policy: ResumeRoutingPolicyId,
    },

    Adapt {
        adapter: EvidenceAdapterId,
        value: ValueId,
    },

    FallbackToVm {
        reason: FallbackReason,
        expr: ExprId,
        bridge: EvidenceToMarkerBridgeId,
    },
}
```

そして result は request-first ではなく、こう分ける。

```rust
enum EvidenceRuntimeResult {
    Value(ValueId),
    DirectAbortive(DirectAbortiveSignal),
    DirectTailResumptive(DirectTailSignal),
    Yield(EvidenceYield),
    FallbackRequest(EvidenceRequest),
}

struct EvidenceYield {
    grant: EvidenceYieldGrant,
    payload: ValueId,
    fragments: Vec<ContinuationFragment>,
    perform_env: EvidenceEnvId,
    resume_policy: ResumeRoutingPolicyId,
}
```

`EvidenceYield` は最初から `EvidenceRequest` を抱えなくていい。ただし **`to_request()` が同値に定義できる**ことは必須だねぇ。現行の `RoutedYield { handler, request }` は橋としてかなり妥当だけど、provider-env route を request-free にする最終形では `handler` だけじゃ足りず、grant/scope/hygiene/call evidence を持つ必要がある。

固定順はこうかなぁ。

### まず固定

```text
EvidenceSlotKey
HandlerEvidence
RoutingPolicy
EvidenceEnv
ProviderGrant
EvidenceCallBoundary
EvidenceAdapter
ResumptionEvidence
FallbackBridge
```

### まだ native に落とさない

```text
multi-shot continuation
ref.update
parser/nondet full specialization
private projection heavy path
```

multi-shot は marker/hygiene boundary on resumed computation が本丸だから、最初の native target にしない方が安全だと思う。既存の staged plan でも、one-shot の後に multi-shot nondet/parser へ進む形になっている。

---

## 私なら次の一手はこれ

1. **`apply_scoped_value_result` を `EvidenceCallBoundary::close` として仕様化する**
   実装関数名はそのままでもいいけど、設計上は「迂回禁止の意味論 primitive」に昇格する。

2. **shortcut に cert を要求する**

```rust
enum CallShortcutCert {
    NoActiveCallMarkers,
    BoundaryAlreadyClosed { plan: HygienePlanId },
    StaticDirectNoResume,
    ProviderGrantGatePassed { grant: ProviderGrantId },
    GuardedDirectTail { snapshot: HygieneSnapshotId },
}
```

`Continuation call shortcut` / `DirectTail` / forced effect fuse は、この cert を持たない限り `apply_scoped_value_result` 相当の close を通す。

3. **ProviderGrant を route から独立した object にする**

```rust
struct ProviderGrant {
    demand_slot: SlotId,
    provider_slot: SlotId,
    handler: HandlerEvidenceId,
    scope: ProviderScopeId,
    hygiene_baseline: HygieneBaseline,
    contract: EffectContractId,
}
```

今の `request_free_yield: bool` はまだ正しい防波堤だと思う。provider-env 由来 route を static direct と同じ扱いにすると、returned thunk / callback hygiene が壊れる理由は「handler pointer はあるが、grant の由来・scope・hygiene・call evidence が足りない」ことだねぇ。

4. **IR dump を先に作る**

既存メモの Stage 1 / 1a そのまま、`EvidenceFunction`, `EvidenceExpr`, `EvidenceSlot`, `EvidenceAdapter` を data-only で dump するのが良い順番だと思う。特に runtime evidence surface は `specialize` の TypeGraph / SolvedTask がまだある段階で出さないと、mono/control IR から復元できない solver-local evidence が落ちる。

---

## まとめると

`scoped marker closure` は value wrapper の問題じゃなく、**call / force / resume / perform の boundary をまたいだ visibility proof** の問題だねぇ。

だから最終形はこう。

```text
current:
  Marked(value, markers)
  Request { guard_ids, carried_guards, handler_boundary, continuation }

next:
  ObjectGraph {
    lexical_evidence,
    provider_grants,
    routing_policies,
    call_boundaries,
    resume_policies,
    fallback_bridges
  }
```

request-free fast path は、request を消す最適化じゃなくて、**request が持っていた hygiene 観測を signal / grant / resumption 側へ移す最適化**。ここを守れば `DirectAbortive` / `DirectTailResumptive` はかなり攻められるけど、`apply_scoped_value_result` の close だけは IR 上で必ず再現する必要があるよ〜。
