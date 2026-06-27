これ、かなりはっきり **今の `request_free_yield: bool` は正しい防波堤**だと思うよ〜。
provider-env 由来の `YieldFallback` を static direct と同じ扱いにした瞬間に壊れるのは、単なる実装バグというより、**route が “handler への直通ポインタ” だけになっていて、provider grant の由来・scope・hygiene・call evidence を表していない**のが本質っぽい。

## まず結論

`DirectYield { handler, request }` は橋渡しとしてかなり妥当だよ〜。ただし、provider-env route を request-free にする最終形では、`DirectYield` は `EvidenceRequest` を抱える形のままではなく、少なくとも **`ProviderGrant` / `RoutedYield` / `EffectThunkEvidence`** みたいな層に分けた方がいい。

今の main では、static `DirectHandlerCall` 由来だけが `request_free_yield: true` で、provider-env 経由の route は `false` に落ちている。これは runtime 側にも「provider-env routes still need the generic request path」とコメントされていて、returned effect thunk の call evidence と handler visibility を揃えるための境界だと明記されているねぇ。

`(each 1..2).list` の canary はまさにそこを踏んでいる。テストは provider env route hit が 0 より大きいこと、control VM と一致すること、結果が `[[1, 2]]` になることを見ている。つまり「callee が返した effect thunk に call evidence が届く」こと自体が仕様面の観測点になっている。

---

## 1. provider-env 由来 handler evidence を request-free にする意味論

### 必要なのは “direct handler call” じゃなくて “scoped provider grant”

provider-env route は、static direct route と同じ `Direct { handler, resumptive, execution }` へ潰すには情報が足りない。

static direct はこう読める。

> この operation call site は、この handler に lexically / hygienically 捕捉されると既に証明済み。

provider-env route は違う。

> この call/action activation の間だけ、ある fallback slot に対して handler evidence capability が渡っている。
> ただし、callback / adapter / delayed boundary / hidden evidence を突破してよいとは限らない。

だから route 表現は最低でもこう分けたい。

```rust
enum EvidenceEffectRoute {
    StaticDirect {
        handler: ExprId,
        handler_id: u32,
        resumptive: bool,
        execution: EvidenceVmOperationExecutionPlan,
    },

    ProviderGrant {
        grant_id: ProviderGrantId,
        demand_slot_id: u32,
        provider_slot_id: u32,
        handler: ExprId,
        handler_id: u32,
        resumptive: bool,
        execution: EvidenceVmOperationExecutionPlan,
        scope: EvidenceProviderScopeId,
        hygiene: ProviderHygieneGate,
    },

    Unhandled,
}
```

いまの runtime は provider route を active provider env から引いている。`effect_route_for_operation_call` は static direct が無ければ active provider env を見て、`provider_route_for_call` から route を取り出す流れだねぇ。 provider env 自体は `with_provider_env` で active stack に積まれ、request / DirectYield / DirectTail の continuation へ閉じ込める実装も既に入っている。

でも `RuntimeEvidenceThunk::Effect` は今のところ `path, payload, route` だけを持つ。つまり、**effect thunk が provider-env route を覚えたとしても、その route がどの call evidence / provider scope / hygiene baseline から来たかを覚えていない**。  これが provider-env `YieldFallback` を雑に request-free 化したときの危険点だと思う。

### request-free provider Yield に必要な実行規則

provider-env 由来の may-yield を request-free にしたいなら、perform/force 時にこういう規則が必要だよ〜。

```text
force effect thunk:
  1. static direct route なら、そのまま direct path
  2. provider grant hint があるなら、
       a. grant scope がまだ有効か見る
       b. call evidence env を復元する
       c. hygiene baseline / marker state を gate に通す
       d. handler body は handler definition env / under env で走らせる
       e. resumption は perform 側 env + provider env を復元して走らせる
  3. gate が落ちたら request fallback
```

この `gate が落ちたら request fallback` が大事。Yulang の hygiene では callback 由来 effect を偶然捕捉しちゃいけない。設計メモにも「catch 全体を provider env として active に積む方向は捨てる」「provider capability + hygiene gate が通るときだけ direct 昇格」とある。

最初の安全な gate は保守的でいい。

```rust
struct ProviderHygieneGate {
    provider_frame_id: EvidenceProviderFrameId,
    marker_plan_len_at_grant: usize,
    active_add_id_len_at_grant: usize,
    active_handler_frame_len_at_grant: usize,
    rejects_after_callback_or_delayed_boundary: bool,
}
```

今の `RuntimeEvidenceProviderFrame` も entry 時の `marker_plan_len / active_add_id_len / active_handler_frame_len` を持って、完全一致のときだけ unshadowed と見なしている。これは初期 gate の材料としてかなりよい形だねぇ。

---

## 2. `DirectYield` が `EvidenceRequest` を内部に持つ今の形は妥当か

妥当。かなり妥当。

理由は、`YieldFallback` は abortive/tail-resumptive と違って、結局は **payload marking / carried guards / handler boundary / continuation capture** が必要になるから。今の `EvidenceRequest` はその全部を持っている。

さらに、`eval_direct_yield_arm` は `visible_operation_resumptive` を通して、見えなければ route を `Unhandled` に戻して request fallback へ送る。つまり DirectYield は「request-free handler call」と「generic request VM」の間の橋として、ちゃんと escape hatch を持っている。

ただ、最終形としては名前と層を分けたい。

```rust
enum EvidenceEvalResult {
    Value(SharedValue),
    Request(EvidenceRequest),

    DirectAbortive(EvidenceDirectAbortive),
    DirectTailResumptive(EvidenceDirectTailResumptive),

    RoutedYield(EvidenceRoutedYield),
}

struct EvidenceRoutedYield {
    grant: EvidenceYieldGrant,
    payload: SharedValue,
    continuation: EvidenceContinuation,
    hygiene_snapshot: HygieneSnapshot,
}

enum EvidenceYieldGrant {
    StaticDirect {
        handler: ExprId,
        handler_id: u32,
    },
    Provider {
        grant_id: ProviderGrantId,
        provider_env: RuntimeEvidenceProviderEnv,
        scope: EvidenceProviderScopeId,
        gate: ProviderHygieneGate,
    },
}
```

そのうえで fallback bridge を持つ。

```rust
impl EvidenceRoutedYield {
    fn to_request(self) -> EvidenceRequest { ... }
}
```

今の `DirectYield { handler, request }` は、この `RoutedYield::StaticDirect` を `EvidenceRequest` ベースで先に作った形だねぇ。static route にはちょうどよい。provider-env route には、`handler: ExprId` だけでは足りない。

---

## 3. Koka-style evidence passing に寄せるなら何を静的に持たせるか

Yulang では Koka の evidence vector をそのまま移植するより、**positive handler evidence + negative/hygiene evidence** の二層にした方が合う。設計メモでも、Koka の row shape だけでは Yulang の hidden/private stack evidence や callback-origin hygiene を消せない、と整理されている。

### Handler object

`EvidenceVmHandlerObjectPlan` は既に `id, handler, slot_id, path, arm_body, arm_class, definition_env` を持っている。ただし `definition_env` は今は空で作られている。

ここを本気で Koka-style に寄せるなら、handler object はこうしたい。

```rust
struct HandlerEvidence {
    id: HandlerEvidenceId,
    handled_slot: SlotId,
    handler_expr: ExprId,
    arm_table: ArmTableId,
    arm_class: EvidenceVmHandlerArmClass,

    // Koka の “handler defined under evidence vector” に相当
    definition_env: EvidenceEnvId,

    // Yulang 固有
    routing_policy: RoutingPolicyId,
    prompt_or_guard_id: EvidenceGuardId,
}
```

Koka 論文メモ側でも handler evidence は「marker / prompt id、handler、handler 定義時 evidence vector」の triple として扱うのが重要だと書かれている。Yulang 側の含意は、handler evidence object が parent / definition evidence route を持つこと、closure/thunk/adapter が evidence env を持つことだねぇ。

### Evidence object / env

今の plan は `EvidenceVmSlotKey { family, route }` を持っていて、route は `Positive / Blocked / UnknownFallback`。direct は positive、hygiene fallback は blocked、fallback requirement は unknown に落ちている。

次は slot key をもう一段濃くする必要がある。

```rust
struct EvidenceSlotKey {
    family: PathId,
    route: EvidenceRouteKey,
    projection_boundary: ProjectionBoundaryId,
    visibility: VisibilityRouteId,
}
```

設計メモにも、slot key は family path だけでは足りず、visibility / blocker route key / projection boundary が要るとある。

### Continuation / resumption

今の continuation は `Then` を含む tree で、`ProviderEnv` frame と `MarkerFrame` frame を持っている。 `ProviderEnv` frame は resume 時に `with_provider_env` で復元される。

Koka-style に寄せるなら、may-yield では `EvidenceRequest` ではなく、まずこれが欲しい。

```rust
enum EvidenceResult {
    Pure(SharedValue),
    Yield(EvidenceYield),
}

struct EvidenceYield {
    grant: EvidenceYieldGrant,
    payload: SharedValue,
    fragments: SmallVec<[ContinuationFragment; 4]>,
    perform_env: EvidenceEnvId,
    resume_policy: ResumeRoutingPolicy,
}
```

Koka メモでも、yield bubbling は「full continuation をすぐ作らず、yield value が上へ泡のように上がりながら continuation fragments を積む」方向として整理されている。

### Thunk / closure / adapter

ここは二種類に分けるのがいい。

```text
lexical evidence:
  closure / thunk / adapter の作成位置で捕捉する evidence env

contract-passed evidence:
  action parameter / returned effect thunk / call activation で渡す provider grant
```

今の runtime は `Closure.provider_env`、`Thunk::Expr.provider_env`、`FunctionAdapter.provider_env` を持っている。  これは lexical evidence としては自然。

でも contract-passed evidence をここへ混ぜると危ない。同じ thunk/action が別 handler に渡されうるし、provider grant は callee の handler scope に依存する。設計メモの `Provided { value, provider_env, scope, contract }` wrapper 案はかなり筋がいい。

---

## 4. provider env route を direct 化する前に追加したい情報

優先順で言うとこれ。

### A. `ProviderGrantPlan`

設計メモの形そのままに近い。

```rust
struct EvidenceVmProviderGrantPlan {
    contract_id: u32,
    demand_slot_id: u32,     // UnknownFallback 側
    provider_slot_id: u32,   // Positive 側
    handler_id: u32,
    handler_expr: ExprId,
    execution: EvidenceVmOperationExecutionPlan,
    hygiene_gate: ProviderHygieneGatePlan,
}
```

既に object graph は slots / function / value / call / handler / operation / provider を分けている。 provider index も same-family handler candidates を作って、`UnknownFallback` を `NeedsEvidenceEnv` に落としている。 でもこれは「候補」までで、「grant witness」ではない。

### B. `EffectContractPlan`

`action: [flip] _` みたいな latent computation は、path 文字列ではなく slot id contract に落とすのがよい。

```rust
struct EvidenceVmEffectContractPlan {
    id: u32,
    owner: EvidenceContractOwner,
    latent_kind: EvidenceLatentKind, // Thunk | Function | Adapter
    required_slots: Vec<u32>,
}
```

設計メモにもこの contract / grant の分離案がある。

### C. `EffectThunkEvidence`

ここが今回の canary 直撃。

今の `RuntimeEvidenceThunk::Effect` は route だけを持つ。provider-env route を request-free にしたいなら、effect thunk はこう持つ必要がある。

```rust
struct EffectThunkEvidence {
    operation_expr: ExprId,
    apply_site: Option<ExprId>,
    demand_slot_id: u32,

    lexical_route_hint: EvidenceEffectRoute,
    call_provider_env: RuntimeEvidenceProviderEnv,

    provider_scope: Option<EvidenceProviderScopeId>,
    hygiene_baseline: HygieneBaseline,
}
```

つまり、`EffectOp` の apply 時に選ばれた bare route ではなく、**その route を選べた理由**を thunk に残す。force 時には `route` を信じるのではなく、`EffectThunkEvidence` から grant を再検証する。

### D. `HandlerObject.definition_env`

ここは埋めたい。今は `definition_env: Vec::new()` で作られている。

DirectTail / DirectAbortive では見えにくいけど、handler body 自体が effect を投げる場合、handler body は operation caller の evidence ではなく、handler 定義側の outer evidence で走る必要がある。Koka の under frame 相当だねぇ。設計メモでも under/blocker context は late marker patch ではなく evidence object shape に入れるべき、とある。

### E. `MayYield` の細分化

今は handler arm class が `Abortive / TailResumptive / MayYield / Fallback / Value`。 分類器も conservative に `MayYield` を返す。

provider-env request-free まで行くなら、`MayYield` は広すぎる。

```text
OneShotYield
MultiShotYield
MayEscapeYield
Fallback
```

`nondet::branch` は method-select handler body で `may-yield` として見えていて、`reject` は abortive として見えている。 `branch` は multi-shot 寄りなので、ここを tail/one-shot と同じ direct continuation で扱うと壊れやすい。

---

## 5. 20x20 nondet を 7ms 近辺へ近づける次の一手

私の推しは二段構え。

```text
意味論の次手:
  thunk/provider env representation

速度の次手:
  Yield/continuation representation + direct-style island
```

### provider route directization

今すぐ `request_free_yield=true` に広げるのは止めた方がいい。canary が示している通り、provider-env route は returned effect thunk の call evidence を運ぶ経路そのものだよ〜。

ただし、`ProviderGrant` と `EffectThunkEvidence` を入れた後なら、provider route directization は有望。現時点のままだと「速いが意味論が壊れる」になる。

### handler inline 化

`DirectAbortive` と `DirectTailResumptive` には効く。ただ、20x20 nondet の中心にいる `branch` は `MayYield` / multi-shot 側なので、handler inline だけでは 7ms 近辺には届きにくいと思う。direct abortive の canary では continuation force / append が 0 になるところまで取れていて、ここは既に良い道ができている。

### direct-style island

これはかなり有望。
`each/list` の周辺で毎回 request/yield VM に戻るのではなく、pure/list/primitive/handler-local loop を direct-style island にして、effect 発生時だけ `Yield` に落ちる形。

Koka メモでも、monadic translation をそのまま box すると遅くなるので、pure fast path は direct に残し、bind は inline / join-point 化する方向が重要だと整理されている。

### continuation representation

ここが 20x20 nondet の本命寄りだと思う。

ただし「Then を front/rear queue にする」だけではなく、**request continuation tree をやめて yield fragments にする**方。今の `continue_routed_request_with_continuation` は continuation frame を見て request に frame を append していく。 May-yield を request surface で扱う限り、multi-shot nondet は request/continuation の再構成コストを踏み続ける。

欲しいのはこれ。

```rust
struct YieldContinuation {
    fragments: SmallVec<[ContinuationFragment; 8]>,
    shared_prefix: Option<ContinuationPrefixId>,
    resume_env: EvidenceEnvId,
    hygiene_resume_plan: MarkerPlanId,
    multi_shot: bool,
}
```

front/rear queue より、**prefix sharing + fragment vector + one-shot/multi-shot flag** の方が筋がいい。

### marker/hygiene state representation

ActiveAddIdIndex で scan 数が減って runtime が悪化したなら、少なくともその workload では「scan 本数」そのものは支配的じゃなかった可能性が高い。main に見える index も debug 比較用で、candidate list を作って sort/dedup する形だから、release hot path に入れると overhead が勝ちやすい構造だねぇ。

marker 側で次にやるなら、index 追加ではなく `MarkerPlanId` 化がよさそう。

```text
PathId
MarkerPlanId
marker transform cache
may_need_hygiene_mark bit
```

設計メモでも、Vec-key cache の再挑戦より concrete guard id を含む `MarkerPlanId` と transform cache が安全、と整理されている。

### thunk/provider env representation

今回の意味論バグに一番近いのはここ。

`RuntimeEvidenceThunk::Effect` が bare route しか持たないままだと、provider-env directization はずっと危ない。逆に、ここを直すと canary を守ったまま provider directization へ進める。だから「次の意味論 work」としては最優先。

---

## 実装順のおすすめ

### 0. 今の bool は残す

`request_free_yield` は一旦このままでよい。static direct route は true、provider-env route は false。ここは防波堤。

### 1. route origin を入れる

```rust
enum EvidenceRouteOrigin {
    StaticDirect,
    ProviderGrant(ProviderGrantId),
}
```

`EvidenceEffectRoute::Direct` に origin を入れるか、`Direct` と `ProviderGrant` を enum variant として分ける。

### 2. `RuntimeEvidenceThunk::Effect` を拡張する

```rust
RuntimeEvidenceThunk::Effect {
    path: Vec<String>,
    payload: SharedValue,
    route_hint: EvidenceEffectRoute,
    evidence: EffectThunkEvidence,
}
```

この段階では挙動を変えず、provider route が来ても `request_free_yield=false` のまま。canary と stats だけ見る。

### 3. `DirectYield` を `RoutedYield` に寄せる

static direct は今と同じ fast path。provider grant は gate を持つ。

```rust
ProviderGrant direct yield:
  if grant_visible_now && hygiene_gate_passes:
      eval handler arm
  else:
      to_request()
```

### 4. handler definition env を埋める

`EvidenceVmHandlerObjectPlan.definition_env` を空のままにしない。handler body effects を caller evidence に混ぜないための under env を入れる。

### 5. `MayYield` を `OneShotYield / MultiShotYield` へ分ける

`nondet::branch` を multi-shot として扱う土台が要る。ここをしないと continuation representation の最適化が曖昧になる。

### 6. request-free provider yield を限定解禁する

条件はかなり強く始めるといい。

```text
- ProviderGrant origin がある
- scope が active / valid
- hygiene baseline が current state と compatible
- handler definition env がある
- continuation が OneShot か、MultiShot 用 fragment representation に乗っている
- fallback bridge がある
```

### 7. 20x20 perf は Yield fragments + direct-style island

ここでようやく 7ms 方向が見えると思う。
provider route directizationは必要条件寄りで、十分条件じゃない。nondet 20x20 は request construction / continuation composition / handler arm dispatch / list aggregation の全体戦なので、**generic request を作らない yield representation** まで行かないと旧 controlVM 最速には寄りにくい。

---

## いちばん短い判断

* **今の `request_free_yield` split は正しい**
* **DirectYield が `EvidenceRequest` を抱える形は橋渡しとして正しい**
* **provider-env route を request-free にするには、bare `handler: ExprId` ではなく `ProviderGrant` が必要**
* **effect thunk は route ではなく call evidence / provider grant provenance を持つべき**
* **20x20 の次の本命は provider directization 単体ではなく、`Yield` representation と continuation fragments**
* **marker index はもう赤信号が出たので、次は scan 削減ではなく `MarkerPlanId` / thunk-provider-env / yield-fragment 側を見るのがよさそうだねぇ**
