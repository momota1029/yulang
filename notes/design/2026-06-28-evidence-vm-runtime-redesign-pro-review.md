うん、これは **marker frame をちょっと速くする話じゃなくて、runtime の中で混ざっている 3 つの機械を分ける話**だねぇ。

私の結論はこう。

> evidenceVM は残す。
> ただし内部表現を、
> **route / yield-request / continuation / marker-scope / provider-scope** に分解する。
> controlVM の snapshot/segment 発想は入れるけど、別 VM として増やすより、まず evidenceVM の backend として入れる方が安全。

現状コードを見る限り、もう方向性はかなり出ているよ〜。`RuntimeEvidenceThunk::Effect` は `route` だけじゃなく `EffectThunkEvidence` を持ち始めていて、provider grant の origin も記録されている。一方で `EvidenceEffectRoute::Direct` はまだ `request_free_yield: bool` で static direct と provider grant を分けているだけで、provider route については「returned effect thunk の call evidence と handler visibility を揃えるため generic request path が必要」とコメントされている。ここが今の防波堤だねぇ。

---

## 0. いちばん大事な見立て

今の太い counter は、たぶんこう読める。

| counter                                          | 読み                                                               |
| ------------------------------------------------ | ---------------------------------------------------------------- |
| `continuation_resume_marker_steps` が巨大           | resume ごとに marker scope を runtime frame として再入場している               |
| `marker_frame_continuation_resume_entries` がほぼ同数 | marker が “値の tag” じゃなく “resume 中の dynamic scope” として効いている        |
| `direct_tail_continuation_then_appends` が巨大      | marker/provider frame が tail append の境界になっていて、`Then` 木へ逃げている     |
| no-continuation DirectTail 0 hit                 | 速くすべき場所は「continuation が無い場合」じゃなく「continuation を segment として運ぶ場合」 |

今の `try_append_owned_tail` は、`MarkerFrame` と `ProviderEnv` の内側へ tail を append しない。コメント通り、そこへ勝手に入れると dynamic marker/provider scope が変わるからねぇ。つまり `Then` が増えるのは実装の怠慢じゃなく、**正しい scope 境界を continuation tree で表現している副作用**だよ〜。

なので redesign の中心はこれ。

> marker/provider を continuation frame から追い出す。
> ただし marker/provider scope を消すんじゃなく、`ScopeDelta` / `MarkerPlanId` / `ProviderScopeToken` として continuation segment に付随させる。

---

## 1. request / marker frame / continuation machine をどう分けるか

今はだいたいこうなっている。

```rust
EvidenceEvalResult
  Value
  Request(EvidenceRequest)
  DirectAbortive
  DirectTailResumptive
  RoutedYield { handler, request }
```

さらに `EvidenceRequest` と `EvidenceDirectTailResumptive` と `EvidenceRoutedYield` が、みんな `EvidenceContinuation` を持つ。`EvidenceContinuation` の中には普通の eval frame だけじゃなく、`MarkerFrame` と `ProviderEnv` も混ざっている。

これを次の 5 層に分けるのがいいと思うよ〜。

### A. `RouteCert`

handler への経路そのもの。

```rust
enum RouteCert {
    StaticDirect {
        handler: ExprId,
        handler_id: u32,
        execution: HandlerExecution,
    },

    ProviderGrant {
        grant_id: ProviderGrantId,
        demand_slot_id: u32,
        provider_slot_id: u32,
        handler: ExprId,
        handler_id: u32,
        scope_id: EvidenceProviderScopeId,
        baseline: HygieneBaseline,
        execution: HandlerExecution,
    },

    Fallback,
}
```

今の code にある `EvidenceResolvedRouteOrigin::ProviderGrant` と `EvidenceProviderGrant` はこの方向へすでに寄っている。provider lookup も `scope_id` と `hygiene_baseline` を持った grant を返す形になっているねぇ。

### B. `EffectSignal`

effect が起きた、という surface。

```rust
enum EffectSignal {
    DirectAbortive(AbortiveCall),
    DirectTail(TailCall),
    Yield(YieldSignal),
    FallbackRequest(GenericRequest),
}
```

`DirectAbortive` と `DirectTail` と `Yield` は request の特殊形じゃなく、別 surface にする。

### C. `EvalContSegment`

純粋な評価 continuation。ここには marker/provider を入れない。

```rust
struct EvalContSegment {
    frames: SmallVec<[EvalFrame; 8]>,
    shared_prefix: Option<ContPrefixId>,
    multiplicity: ContinuationMultiplicity,
}
```

`EvalFrame` は `ApplyArg`, `CaseScrutinee`, `SelectBase`, `BlockStmt` みたいな ordinary frame だけ。`MarkerFrame` / `ProviderEnv` はここから外す。

### D. `ScopeDelta`

continuation が resume される時に復元する dynamic scope。

```rust
struct ScopeDelta {
    marker_resume_plan: Option<MarkerPlanId>,
    provider_env: Option<ProviderEnvId>,
    handler_boundary: Option<HandlerBoundaryId>,
    hygiene_snapshot: HygieneSnapshot,
}
```

今の `with_provider_env` は、request / routed yield / direct tail の continuation に provider env frame を閉じ込めている。これは意味論として正しいけど、continuation frame に混ぜるから append/resume が重くなる。`ScopeDelta` へ分けるのが筋だねぇ。

### E. `GenericRequest`

fallback 専用。昔の `EvidenceRequest` に近い。

```rust
struct GenericRequest {
    path: PathId,
    payload: SharedValue,
    route_hint: RouteCert,
    guards: GuardSet,
    continuation: YieldContinuation,
}
```

重要なのは、**request を共通表現にしない**こと。
request は「証明できなかった時の互換 fallback」に下げる。

---

## 2. Yulang hygiene marker は Koka 的 evidence passing と相性よく再解釈できるか

できる。ただし Koka 風の “positive evidence vector” だけだと足りない。

Yulang の hygiene marker は、こう再解釈するのが一番きれいだと思うよ〜。

> handler evidence は positive capability。
> hygiene marker / AddId / boundary は negative capability。
> provider grant は positive capability と negative capability の両方を含む certificate。

つまり:

```rust
struct EvidenceCell {
    slot_id: SlotId,
    handler_id: HandlerId,
    handler_expr: ExprId,
    handler_definition_env: EvidenceEnvId,

    // Yulang 固有
    scope_id: EvidenceProviderScopeId,
    hygiene_baseline: HygieneBaseline,
    marker_epoch: MarkerEpoch,
    add_id_epoch: AddIdEpoch,
    handler_epoch: HandlerEpoch,
}
```

callback boundary を越える時は、これをそのまま渡しちゃだめ。

```rust
enum EvidenceTransfer {
    Keep(EvidenceCell),
    Guard(EvidenceCell, HygieneGate),
    Drop,
}
```

`action: [flip] _` みたいな annotation は、「外側 handler を ambient に有効化する」じゃなくて、**その action activation に handler capability を渡せる contract** と読むのが安全だねぇ。design note でも、catch 全体を provider env として active に積む方向は callback hygiene を壊すから捨てるべき、と整理されている。

ここでの落とし穴は、marker を「値に付く tag」だけとして見ること。

現コードでは marker frame を閉じる時、request payload を mark するだけじゃなく、resume continuation 側にも `MarkerFrame` を入れている。`close_marker_request`, `close_marker_direct_tail`, `close_marker_routed_yield` がそれぞれ resume marker を continuation に積む形だねぇ。

だから `carry_after_frame == false` の AddId でも、resume 中には意味が残る場合がある。
これは “marker plan-only 化” で消しちゃいけないやつ。

---

## 3. `DirectTailResumptive` / `DirectAbortive` / fallback request をどういう IR に分けるか

私はこの IR 分割がよさそうだと思う。

```rust
enum HandlerExecution {
    Abortive,
    TailResumptive,
    OneShotYield,
    MultiShotYield,
    MayEscapeYield,
    Fallback,
}
```

その上で runtime result をこう分ける。

```rust
enum EvidenceEvalResult {
    Value(SharedValue),

    DirectAbortive(DirectAbortiveCall),
    DirectTail(DirectTailCall),

    Yield(YieldSignal),

    Request(GenericRequest),
}
```

### `DirectAbortive`

最も安全。

```rust
struct DirectAbortiveCall {
    cert: RouteCert,
    handler: ExprId,
    payload: SharedValue,
    payload_marker_policy: MarkerPolicy,
}
```

continuation を持たない。
provider grant 由来でも、scope と baseline が clean なら request-free にしやすい。

現コードでも `DirectAbortive` は continuation append を避ける扱いになっている。`force_effect_result` は direct abortive route を見たらすぐ `EvidenceEvalResult::DirectAbortive` を返す。

### `DirectTail`

これは “continuation object を作らない” ではなく、**one-shot segment として持つ**のが正しい。

```rust
struct DirectTailCall {
    cert: RouteCert,
    handler: ExprId,
    payload: SharedValue,
    resume_segment: EvalContSegment,
    scope_delta: ScopeDelta,
    marker_policy: ResumeMarkerPolicy,
}
```

今の direct-tail は request boundary が無ければ continuation を call に append する。ただし append 先が marker/provider frame を含む tree なので、`Then` が増える。

ここを `EvalContSegment + ScopeDelta` に分けると、marker/provider frame が append boundary にならなくなる。

### `Yield`

`YieldFallback` / one-shot / multi-shot は request と分ける。

```rust
struct YieldSignal {
    cert: RouteCert,
    handler: Option<ExprId>,
    payload: SharedValue,
    continuation: YieldContinuation,
    hygiene: HygieneSnapshot,
}

struct YieldContinuation {
    fragments: SmallVec<[ContinuationFragment; 8]>,
    shared_prefix: Option<ContPrefixId>,
    scope_delta: ScopeDelta,
    multiplicity: ContinuationMultiplicity,
}
```

`RoutedYield { handler, request }` は橋渡しとしてはあり。でも最終形では `request` を中に持たない方がいい。
`to_request()` を fallback bridge として持つ、くらいがきれい。

### `GenericRequest`

これは最後の逃げ場。

入れる条件はこのへん。

| fallback へ落とす条件                                | 理由                  |
| ---------------------------------------------- | ------------------- |
| `HygieneFallback` / `BlockedFallback`          | hygiene が主語         |
| delayed boundary                               | 捕捉順序が変わる            |
| provider grant の scope が死んでいる                  | stale capability    |
| baseline 以降に matching AddId / handler shadow   | callback leakage 防止 |
| `MultiShotYield` なのに fragment sharing 未実装      | continuation 複製が必要  |
| ref-set / handler boundary など request boundary | 現行 semantics が安全    |

今の plan は static `DirectHandlerCall` だけ `request_free_yield: true`、`LexicalHandlerCandidate` / `HygieneFallback` / `GenericFallback` は static route 上では `Unhandled` にしている。provider lookup 側は candidate を作るけど、`request_free_yield: false` にしている。ここはかなり健全な分割だよ〜。

一点だけ警戒したいのは、`MayEscapeYield` を `DirectTailResumptive` に落としている箇所。名前通り “may escape” なら direct-tail 扱いは危ない。classifier 上の意味が “tail escape だけ” なら名前を変えた方がよさそうだねぇ。

---

## 4. continuation resume 時の marker scope を軽量化する canonical な方法

canonical にはこれ。

> `MarkerFrame` を continuation frame として保存しない。
> `ResumeMarkerPlan` を `ScopeDelta` として保存する。
> resume 時に必要な時だけ dynamic scope を activate する。

今の重さは、`resume_marker_frame` が marker frame を再 push して、active marker plan も push して、その中で `resume_continuation` するところにある。

代替はこう。

```rust
enum ResumeMarkerPlan {
    Empty,

    // 値だけ mark すればよい。dynamic AddId は不要。
    PureValueMark {
        markers: MarkerSliceId,
        type_filter: TypeMarkPolicy,
    },

    // resume 中だけ AddId / handler boundary が効く。
    DynamicScope {
        scope_id: RuntimeMarkerScopeId,
        enter_ops: SmallVec<[MarkerEnterOp; 4]>,
        value_mark: MarkerSliceId,
        handler_boundary: Option<HandlerBoundaryPlanId>,
    },
}
```

そして continuation にはこう持たせる。

```rust
struct ScopeDelta {
    resume_marker_plan: ResumeMarkerPlanId,
    provider_scope_delta: Option<ProviderScopeDeltaId>,
}
```

### ここで絶対にやっちゃいけないこと

`markers_for_continuation_resume(&markers)` が空じゃないのに、単に marker frame を消すこと。

それをやると、callback 由来の effect が resume 中に外側 handler へ漏れる。
特に `carry_after_frame == false` は「request payload には carry しない」だけで、「resume 中の dynamic blocker として不要」という意味じゃない。

### 軽量化の順番

1. `Rc<[EvidenceValueMarker]>` から `RuntimeMarkerPlanId` を作る
   既存 marker vector を intern するだけ。意味は変えない。

2. `MarkerFrame` continuation を `ScopedResume { plan_id, next }` に置き換える
   最初は `ScopedResume` が内部で今と同じ push/pop をやる。

3. `ResumeMarkerPlan::PureValueMark` の時だけ push/pop を省く
   active AddId も handler boundary もいらない場合だけ。

4. `DynamicScope` は compact enter op へする
   marker vector 全体を毎回走査しない。`Frame/AddId` の enter ops を precompute する。

5. DirectTail / YieldContinuation では `ScopeDelta` として運ぶ
   `Then` tree の中へ marker frame を入れない。

この順番なら、marker plan-only 化の regression を避けやすい。
「計画だけにする」んじゃなく、「resume dynamic scope と value marking を分離する」のが肝だねぇ。

---

## 5. controlVM の frame segment / snapshot に近い表現を evidenceVM に入れるか、別 VM にするか

**evidenceVM の中へ backend として入れる**のがいいと思う。

別 VM にすると、hygiene / provider grant / continuation multiplicity / request fallback の仕様が二重化する。今の evidenceVM はすでに provider frame、scope id、hygiene baseline、provider env continuation close を持っている。ここを捨てて別 VM を作ると、速いけど意味がズレる branch になりやすい。

おすすめはこう。

```rust
enum ContinuationBackend {
    Tree(EvidenceContinuation),        // 現行互換
    Segment(EvalContSegment),          // 新 backend
}

enum ScopeBackend {
    FrameTree,                         // 現行 MarkerFrame / ProviderEnv
    Delta(ScopeDelta),                 // 新 backend
}
```

最初は `Segment` を作っても `to_tree()` で旧 path に戻せるようにする。
これなら `compare.control: match` を維持しながら、一部 workload だけ新表現に乗せられる。

### どこから segment 化するか

優先順はこれ。

1. `DirectTailCall.resume_segment`
2. `YieldSignal.continuation.fragments`
3. generic request の `continuation`
4. 通常 eval loop の full direct-style stack

generic request からやると、いきなり hygiene の全ケースを踏む。
`DirectTail` から入る方が小さい。

---

## 6. native / direct-style island 前に固定すべき runtime evidence surface

native island へ行く前に、最低限これを固定した方がいいよ〜。

### 固定 1: route provenance

`handler: ExprId` だけでは足りない。

```rust
RouteCert {
    origin,
    handler_id,
    demand_slot_id,
    provider_slot_id,
    scope_id,
    baseline,
    execution,
}
```

今の `EffectThunkEvidence { route_origin }` は入口として良いけど、最終的には `route_origin` だけじゃなく `cert` そのものを持たせたい。`RuntimeEvidenceThunk::Effect` が `route` と `evidence` を持っている今の形は、この拡張にちょうどよい足場だねぇ。

### 固定 2: lexical evidence と contract-passed evidence の区別

* closure/thunk/adapter が作成位置で捕まえるもの: lexical evidence
* `action: [flip] _` などで activation に渡すもの: contract-passed evidence

これを混ぜると、同じ action が別 handler scope に渡った時に漏れる。

```rust
RuntimeEvidenceValue::Provided {
    value: SharedValue,
    grant_env: ProviderEnvId,
    contract_id: ContractId,
    scope_id: EvidenceProviderScopeId,
}
```

### 固定 3: handler definition env

handler body は caller evidence で走るんじゃなく、handler 定義側の evidence env で走る必要がある。Koka 的には under env 相当。
ここを空のまま direct-style island に行くと、handler body 内 effect の捕捉先がズレる危険がある。

### 固定 4: yield surface

`RoutedYield { handler, request }` を最終 surface にしない。

```rust
YieldSignal {
    cert,
    payload,
    continuation,
    scope_delta,
    fallback_to_request,
}
```

### 固定 5: marker policy

```rust
struct MarkerPolicy {
    payload: PayloadMarkerPolicy,
    resume: ResumeMarkerPlanId,
    call_boundary: CallMarkerPolicy,
}
```

payload mark と resume dynamic scope を同じ `MarkerFrame` で表現し続けると、direct-style island がいつまでも request machine を引きずる。

### 固定 6: continuation multiplicity

```rust
enum ContinuationMultiplicity {
    OneShotOwned,
    MultiShotShared,
    MayEscape,
}
```

ここを固定しないまま native island に入ると、multi-shot nondet で破綻しやすい。

---

## 段階的な移行計画

### Phase 0: invariant と canary を固定

ここは速度改善なしでいい。

固定する test:

* callback 由来 effect を外側 handler が捕捉しない
* `carry_after_frame == false` AddId が resume 中に必要なケース
* same-family nested handler shadow
* delayed boundary
* provider scope escape
* returned effect thunk が call evidence を保持するケース
* nondet 20 discard
* showcase
* `compare.control: match`

counter は今のものに加えて、これが欲しい。

```text
yield_signal_created
yield_signal_to_request
yield_signal_direct_static
yield_signal_direct_provider
resume_marker_plan_empty
resume_marker_plan_pure_value
resume_marker_plan_dynamic_scope
direct_tail_segment_appends
direct_tail_tree_fallbacks
provider_grant_clean_hits
provider_grant_dirty_fallbacks
```

### Phase 1: route cert を first-class 化

今の:

```rust
EvidenceEffectRoute::Direct { handler, resumptive, execution, request_free_yield }
```

をこう寄せる。

```rust
EvidenceEffectRoute::Direct {
    cert: RouteCertId,
    handler: ExprId,
    execution: HandlerExecution,
}
```

ただし最初は内部で今の情報へ戻すだけ。挙動は変えない。

この段階で `request_free_yield` は消さず、`RouteCert::StaticDirect` だけ true 相当、`ProviderGrant` は false 相当のままにする。

### Phase 2: `RoutedYield` を request から剥がす

今の:

```rust
EvidenceRoutedYield {
    handler,
    request,
}
```

をこうする。

```rust
EvidenceRoutedYield {
    cert: RouteCertId,
    handler: ExprId,
    payload: SharedValue,
    continuation: YieldContinuation,
    marker_policy: MarkerPolicy,
}
```

ただし `YieldContinuation` は最初、旧 `EvidenceRequest` を内部に持って `to_request()` するだけでいい。
ここで速度を狙わない。surface を固定するのが目的。

### Phase 3: `ResumeMarkerPlanId` を入れる

`close_marker_request` / `close_marker_direct_tail` / `close_marker_routed_yield` が直接 `EvidenceContinuation::marker_frame(...)` を作るのをやめる。

最初は:

```rust
ResumeMarkerPlanId -> old MarkerFrame
```

へ戻すだけでいい。次に `PureValueMark` だけ push/pop を省く。

### Phase 4: DirectAbortive provider grant を限定解禁

条件は強く始める。

```text
RouteCert::ProviderGrant
scope alive
baseline exact
no AddId shadow
no handler shadow
not delayed
not hygiene fallback
execution = Abortive
```

これなら continuation が絡まないので、最初の request-free provider route として安全。

### Phase 5: DirectTail を owned segment 化

今の `continue_direct_tail_resumptive_with_continuation` は frame を剥がしながら `append_direct_tail_continuation` していく。これを、request boundary までの ordinary frame を `EvalContSegment` として一括 capture する。

```rust
fn split_until_request_boundary(cont, target_handler)
  -> Result<(EvalContSegment, ScopeDelta, RestCont), Fallback>
```

最初は `MarkerFrame` / `ProviderEnv` が出たら fallback。
次に `ScopeDelta` へ移す。

### Phase 6: Yield fragments

nondet の本命はここだと思う。

`YieldFallback` を request として泡上げするんじゃなく、

```rust
YieldSignal {
    fragments,
    shared_prefix,
    multiplicity,
}
```

で泡上げする。

multi-shot は `shared_prefix` に freeze。one-shot は owned。
ここまで来ると `continuation_resume_marker_steps` と `direct_tail_continuation_then_appends` の両方を構造的に減らせる。

### Phase 7: direct-style island

最後にやる。

```rust
expr_fast_class[ExprId] =
    PureIsland
  | LocalEffectIsland
  | EvidenceIsland
  | GenericIsland
```

pure/list/primitive/local handler loop を direct に残して、effect が出た時だけ `YieldSignal` に落とす。
でもこれは `YieldSignal` と `ScopeDelta` が固まってからがいい。先にやると request VM を island の境界へ持ち込むだけになりやすい。

---

## 失敗しやすい設計

これは明確に止めた方がいいやつ。

### 1. provider route を `Direct { handler }` に潰す

`handler` が見えることと、provider grant が hygienic に有効なことは違う。
callback 由来 effect を外側 handler が拾う事故が起きる。

### 2. catch 全体を provider env として active にする

これは design note の通り危険。`action` activation に渡す capability と、catch body 全体の ambient handler は別物。

### 3. marker frame を単純に plan-only 化する

payload marking と resume dynamic scope が混ざっているから、消すと regression が出る。
やるなら `PayloadMarkerPolicy` と `ResumeMarkerPlan` に分ける。

### 4. `carry_after_frame == false` を resume で無視する

request payload に carry しないことと、resume 中に blocker として不要なことは別。ここは特に危ない。

### 5. ActiveAddId の index を太い runtime hot path に入れる

候補 list 作成、sort/dedup、prefix relation があると、scan より重くなりがち。もう一度やるなら index じゃなく epoch / plan id / scope cert 側がよさそう。

### 6. separate VM を本線にする

速い VM と正しい VM が分裂する。
やるなら `SegmentBackend` を evidenceVM 内に差し込む形が安全。

---

## 最初に実装すべき最小スライス

私ならこれを最初に切る。

### Slice: `RoutedYield` / `RouteCert` / `ResumeMarkerPlanId` の surface 分離

速度改善は小さくてもいい。ここを固めると、その後の DirectTail segment と Yield fragments が安全に入る。

#### 1. `RouteCert` を導入

既存の `EvidenceRouteOrigin` / `EvidenceProviderGrant` をまとめる。

```rust
enum RouteCert {
    StaticDirect { handler, handler_id, execution },
    ProviderGrant { grant_id, handler, handler_id, scope_id, baseline, execution },
    Fallback,
}
```

`EvidenceEffectRoute::Direct` は当面これを参照するだけ。

#### 2. `EffectThunkEvidence` を拡張

今の:

```rust
struct EffectThunkEvidence {
    route_origin: Option<EvidenceRouteOrigin>,
}
```

をこうする。

```rust
struct EffectThunkEvidence {
    cert: RouteCertId,
    apply_site: Option<ExprId>,
    operation_expr: ExprId,
    demand_slot_id: u32,
    provider_scope: Option<EvidenceProviderScopeId>,
    hygiene_baseline: HygieneBaseline,
}
```

最初は未使用 field があってもいい。
大事なのは「force 時に bare route を信じる」設計から抜けること。

#### 3. `EvidenceRoutedYield` から `request` を剥がす

```rust
struct EvidenceRoutedYield {
    cert: RouteCertId,
    handler: ExprId,
    payload: SharedValue,
    continuation: YieldContinuation,
    marker_policy: MarkerPolicy,
}
```

ただし内部 bridge として:

```rust
impl EvidenceRoutedYield {
    fn to_request(self) -> EvidenceRequest
}
```

を持つ。既存挙動は全部 `to_request()` に逃がしていい。

#### 4. `ResumeMarkerPlanId` を導入

`close_marker_*` では直接 `EvidenceContinuation::marker_frame` を作らず、まず plan 化する。

```rust
let plan = self.resume_marker_plan(markers, activate_add_ids, handler_path);
continuation = continuation.with_scope_delta(plan);
```

最初は `with_scope_delta(plan)` が旧 `MarkerFrame` を作るだけでいい。

#### 5. provider grant directization はまだ広げない

`request_free_yield` は残す。
static direct は今まで通り。provider grant は fallback 寄りのまま。

この slice の完了条件:

```text
compare.control: match
nondet/showcase 結果一致
callback hygiene canary 一致
carry_after_frame resume canary 一致
stats 上で surface 分離だけ確認
```

---

## その次の一手

最小 slice の次は、これ。

### DirectAbortive provider grant fast path

```text
ProviderGrant
+ Abortive
+ scope alive
+ baseline clean
+ no AddId shadow
+ no handler shadow
+ not delayed
```

ここだけ request-free にする。continuation がないから、最初の実測改善として安全。

### DirectTail segment

次に、`DirectTail` の continuation を `EvalContSegment` にする。
ただし最初は marker/provider を含む continuation は旧 path へ fallback。

```rust
if let Some(segment) = cont.try_extract_plain_segment_until(handler) {
    call.resume_segment = segment;
} else {
    old_path();
}
```

no-continuation fast path が 0 hit だった以上、狙うべきはここだねぇ。

---

## まとめると

* **request は共通表現から fallback 表現へ降ろす**
* **marker/provider は continuation frame から ScopeDelta へ移す**
* **handler direct route は `handler ExprId` じゃなく `RouteCert` にする**
* **Yulang hygiene は Koka 的 positive evidence に negative evidence を足したものとして扱う**
* **DirectAbortive → DirectTail segment → Yield fragments → direct-style island の順が安全**
* **最初の実装 slice は速度より surface 分離を優先する**

一番効きそうな本丸は、`Then` を別の木に変えることじゃなくて、**continuation tree の中に marker/provider scope を混ぜない表現へ移ること**だと思うよ〜。
