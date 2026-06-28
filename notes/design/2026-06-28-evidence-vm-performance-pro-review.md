GitHub の実装も見ると、いちばん大きいのは **provider lookup の高速化じゃなくて、request / marker / continuation を通らない evidence-direct 実行経路を作ること** だと思うよ〜。

今の runtime は、effect op apply で `Thunk::Effect` を作って、force 時に `DirectAbortive` / `DirectTailResumptive` / `RoutedYield` / `Request` へ分岐する形だねぇ。direct-tail 自体の分岐はもうあるけど、provider 由来 route は `request_free_yield: false` で、grant gate が通らないと結局 request に落ちる構造になっている。

## まず結論

**最大効果候補はこれ:**

> `DirectHandlerCall` だけを direct と数える設計から、
> **evidence grant 付き provider route を「hygiene 証明済み direct route」として扱う層**を追加する。
> そのうえで、abortive / tail-resumptive / one-shot の一部だけ request-free にする。

つまり `plan_direct_effect_routes` を無理に増やすというより、別カウンタとして

```text
plan_static_direct_effect_routes
plan_evidence_direct_effect_routes
plan_request_free_effect_routes
plan_marker_free_effect_routes
```

を持つ感じがよさそうだねぇ。

今の `plan_direct_effect_routes` は `DirectHandlerCall` だけを direct route にしていて、`LexicalHandlerCandidate` / `HygieneFallback` / `GenericFallback` は static route 上では `Unhandled` 扱いだよ〜。 ただし runtime plan には provider lookup があって、`LexicalHandlerCandidate delayed=false` などから provider route を返せる仕組みはもう入っている。

なので、今の状態はこう見るとよさそうだねぇ。

| 見えているもの                                | 解釈                                             |
| -------------------------------------- | ---------------------------------------------- |
| `plan_direct_effect_routes: 0`         | static lexical route は取れていない                   |
| provider env route lookups がある         | evidence 経由の route は実行時に探している                  |
| direct tail continuation appends がほぼ 0 | 見つけた route が request-free fast path に乗れていない    |
| marker resume / request append が巨大     | lookup より delimited continuation machinery が本丸 |

---

# 1. いちばん大きく速くなる可能性がある設計変更

## A. evidence-direct route を first-class にする

今の static direct は `ControlEvidenceRoute::Direct` 由来だけど、provider env route は runtime lookup 後に `EvidenceResolvedRouteOrigin::ProviderGrant` を持つ形だねぇ。`scope_id` と `hygiene_baseline` も grant に入っている。

この grant を「単なる lookup 結果」じゃなくて、**direct 実行の証明オブジェクト**に昇格させるのが大きいと思う。

```rust
enum RuntimeRouteCert {
    StaticDirect {
        handler: ExprId,
    },
    EvidenceDirect {
        handler: ExprId,
        handler_id: u32,
        demand_slot_id: u32,
        provider_slot_id: u32,
        scope_id: EvidenceProviderScopeId,
        hygiene_baseline: EvidenceProviderHygieneBaseline,
        path_id: PathId,
        execution: EvidenceVmOperationExecutionPlan,
        fast_path: FastPathClass,
    },
}
```

`FastPathClass` は例えば:

```rust
enum FastPathClass {
    AbortiveRequestFree,
    TailResumptiveRequestFreeMarkerFree,
    TailResumptiveRequestFreeMarked,
    YieldFallbackRouted,
    GenericRequest,
}
```

### 期待効果

かなり大きい。代表 workload が effect/resume 密なら、**1.5〜3x 級**の余地があると思う。もっとも、handler arm が `YieldFallback` や multi-shot に多く落ちるなら効果は縮む。

### リスク

hygiene を壊すリスクがいちばん大きい。特に「同じ path の handler が見える」だけで direct 化すると危ない。callback 由来 effect を外側 handler が拾う事故が起きる。

### 必要な plan / runtime evidence

* route の由来: static / provider grant / fallback
* handler object id
* provider slot id / demand slot id
* provider scope id
* hygiene baseline
* operation path id
* handler arm class
* delayed boundary の有無
* callback boundary の有無
* marker-free 条件
* request boundary-free 条件

---

# 2. `plan_direct_effect_routes: 0` のまま速くする道はあるか

ある。ただし、**今の意味の `plan_direct_effect_routes` は増えなくても、別種の direct route を増やす必要がある**と思う。

今の runtime は、static direct がなければ active provider env を見て route を探す。`effect_route_for_operation_call` は static route を先に見て、なければ provider lookup を試す構造になっている。

だから `plan_direct_effect_routes: 0` のままでも、

```text
provider route lookup
  -> evidence grant
  -> direct-tail / abortive fast path
```

へ入れれば速くできる。

ただ、今の stats で `direct_tail_continuation_appends` がほぼ 0 なら、provider route が見つかっても以下のどこかで request path に落ちているはずだねぇ。

* route hit していない
* hit しているが `execution` が `YieldFallback`
* `provider_grant_path_gate_passes` が落ちている
* marker / handler shadow がある扱いになっている
* continuation に request boundary がある
* direct-tail 化しても catch 側 visibility で request に戻っている

なので、まず増やすべきカウンタはこれ。

```text
provider_route_hits_by_execution:
  direct_abortive
  direct_tail_resumptive
  yield_fallback
  blocked_fallback
  generic_fallback

direct_tail_gate_fail_reasons:
  no_grant
  grant_scope_missing
  handler_shadowed
  add_id_shadowed
  request_boundary
  handler_not_visible
```

`plan_direct_effect_routes: 0` を気にしすぎるより、**provider route hit が direct-tail へ入っているか**を見たほうがいいよ〜。

---

# 3. hygiene を壊さずに request-free / marker-free fast path を作る条件

ここはかなり大事。

今の code にはすでに grant gate がある。`request_free_yield || provider_grant_gate_passes(...)` や、direct-tail 用の `provider_grant_path_gate_passes(...)` があって、scope id / baseline / path shadow を見ている。

これを fast path の正式条件にするのが筋だねぇ。

## request-free 条件

最低限これ。

| 条件                                                     | 理由                                       |
| ------------------------------------------------------ | ---------------------------------------- |
| route が `StaticDirect` または `EvidenceDirectGrant`       | handler が偶然の外側 handler ではない証拠            |
| `HygieneFallback` ではない                                 | callback boundary を突破しない                 |
| `delayed_boundary == false`                            | delayed boundary は捕捉順序が危ない               |
| `provider scope` がまだ active                            | 古い grant を使わない                           |
| baseline 以降に同 path handler shadow がない                  | 外側/内側 handler 混同を防ぐ                      |
| baseline 以降に path に合う add-id marker がない                | callback hygiene を守る                     |
| handler arm が abortive or tail-resumptive              | continuation を request object として渡す必要がない |
| continuation が target handler まで request boundary-free | catch/refset/value boundary を飛び越さない      |

## marker-free 条件

request-free よりさらに強い。

| 条件                                                               | 理由                                    |
| ---------------------------------------------------------------- | ------------------------------------- |
| payload type が hygiene mark 不要、または marker list empty             | payload marking を省ける                  |
| resume value type が hygiene mark 不要、または resume marker list empty | continuation resume marking を省ける      |
| active marker plan が empty、または path に対して inert                   | function call marker を省ける             |
| handler boundary が不要                                             | `handler_boundary_for_request` 相当を省ける |
| callback adapter 由来ではない                                          | adapter は body/arg/ret marker が絡む     |

今の marker frame は request payload と continuation resume 側に marker を積む設計で、`close_marker_request` / `close_marker_direct_tail` / `close_marker_routed_yield` がそれぞれ continuation に `MarkerFrame` を足している。 ここを省くには「省いても同じ marker が空になる」という証明が必要だよ〜。

## runtime plan に持たせたい証拠

```rust
struct EffectFastPathCert {
    route_kind: RouteKind,
    handler_id: u32,
    handler_expr: ExprId,
    path_id: u32,

    demand_slot_id: u32,
    provider_slot_id: u32,

    // hygiene
    provider_scope_id: Option<u32>,
    provider_baseline: HygieneBaseline,
    no_delayed_boundary: bool,
    no_callback_boundary: bool,
    not_hygiene_fallback: bool,

    // shadow checks can be dynamic epoch compare
    handler_epoch_at_grant: u32,
    add_id_epoch_at_grant: u32,
    marker_epoch_at_grant: u32,

    // continuation
    arm_class: EvidenceVmHandlerArmClass,
    continuation_class: ContinuationFastPathClass,

    // marker
    payload_marker_policy: MarkerPolicy,
    resume_marker_policy: MarkerPolicy,
}
```

epoch 化すると、毎回 vector slice scan せずに

```text
current_handler_epoch[path] == grant.handler_epoch
current_add_id_epoch[path] == grant.add_id_epoch
current_marker_epoch == grant.marker_epoch
```

みたいに見られる。既存の `active_add_ids[baseline..]` scan を fast path の条件判定から追い出せるのが大きいねぇ。

---

# 4. Koka 的 evidence passing に寄せるなら何を変えるべきか

今の provider env は「runtime value が provider env を持ち、実行中だけ active stack に積み、effect call 時に lookup」だねぇ。closure / thunk / adapter が provider env を保持して、apply/force 時に `with_provider_env` する構造になっている。

Koka 的に寄せるなら、lookup stack よりも **hidden evidence parameter** に寄せる。

## 変える方向

```text
今:
  effect call
    -> active provider env stack を見る
    -> slot と handler candidate を照合
    -> route を得る

Koka 寄せ:
  function(evidence_slot_0, evidence_slot_1, normal_arg)
    -> effect call は local evidence cell を直接読む
    -> handler token を direct call
```

### Evidence cell の形

```rust
struct EvidenceCell {
    slot_id: u32,
    handler_id: u32,
    handler_expr: ExprId,
    arm_body: ExprId,
    arm_class: EvidenceVmHandlerArmClass,
    provider_scope_id: u32,
    hygiene_baseline: EvidenceProviderHygieneBaseline,
    handler_epoch: u32,
    add_id_epoch: u32,
}
```

関数 plan はこうなる。

```rust
struct FunctionEvidenceSignature {
    required_slots: Vec<SlotId>,
    provided_slots: Vec<SlotId>,
    captured_slots: Vec<SlotId>,
}
```

call site は hidden args を渡す。

```text
call f(x)
  -> call f(evidence[s0], evidence[s3], x)
```

closure は provider env ではなく、**必要 slot の evidence cell 配列**を持つ。

```rust
Closure {
    env,
    evidence_cells: SmallVec<[EvidenceCell; 2]>,
}
```

## hygiene 上の肝

evidence cell は「handler そのもの」じゃなくて、**handler + hygiene baseline + scope token**だよ〜。

callback boundary を越えるときは evidence cell をそのまま渡さない。以下のどちらかにする。

1. evidence cell を削る
2. guarded evidence cell に落として、force 時に epoch/gate を再検査する

これで「callback 由来 effect を外側 handler が偶然捕捉する」を防げる。

---

# 5. direct-style island / pure island / effect island 分離は有効か

有効。ただし、最初から大きな compiler lowering をやるより、**runtime plan の分類として入れる**のが安全だと思う。

## island 分類

| island              | 条件                                                          | 実行                               |
| ------------------- | ----------------------------------------------------------- | -------------------------------- |
| pure island         | effect call なし、provider env なし、marker 不要                    | 通常 direct interpreter / stack VM |
| local effect island | handler と operation が同じ island 内、hygiene fallback なし        | evidence-direct fast path        |
| evidence island     | hidden evidence params で必要 handler が渡る                      | provider lookup なし               |
| generic island      | callback boundary / delayed boundary / multi-shot / unknown | 現行 request path                  |

この分離は `examples/showcase.yu` みたいに pure code と effect code が混ざる workload で効きやすいはずだねぇ。pure island では provider env も marker plan も触らない。effect island では request を作らない。generic island だけ現行 machinery に戻す。

### 実装の第一歩

`RuntimeEvidenceExpr` にいきなり bytecode VM を入れる前に、plan にこれを足すだけでいい。

```rust
expr_fast_class[ExprId] = Pure | LocalEffect | EvidenceEffect | Generic
```

それで eval 側に小さい fast branch を足す。

---

# 6. continuation 表現を linked list / queue / rope / stack machine に変える価値

価値はある。ただし、**request-free 化より優先度は一段下**かなぁ。

今の continuation は `Identity | Frame(Rc<Frame>)` で、`Then { first, second }` を作る。append は `Rc::get_mut` できたら tail に破壊的 append、無理なら `Then` を作る形だねぇ。

さらに marker/provider frame は tail append の境界になっていて、tail を中へ入れないようにしている。これは意味論上正しいけど、`Then` と resume step が増えやすい。

## おすすめの順

### 1. one-shot owned continuation stack

```rust
enum Continuation {
    Owned(SmallVec<[Frame; 8]>),
    Shared(Rc<SharedContinuation>),
}
```

通常評価・tail resumptive は `Owned`。continuation が値として逃げる、multi-shot、marked continuation になった時だけ `Shared` へ freeze。

これは効果が出やすい。

### 2. continuation segment + scope delta

request に丸ごと continuation を append する代わりに、

```rust
Request {
    continuation_segment: ContSegmentId,
    scope_delta: ScopeDelta,
}
```

みたいに持つ。marker/provider frame を通常 frame と混ぜず、scope enter/exit として扱う。

### 3. rope は後回し

rope は multi-shot continuation が多いなら有効だけど、今の数字だと `Then` 木そのものより、request/marker の意味処理が太そうだねぇ。rope だけ入れても「きれいな遅さ」になりがち。

---

# 7. 効果が薄い / hygiene を壊しやすい最適化

## 薄そう

| 案                       | 理由                                                           |
| ----------------------- | ------------------------------------------------------------ |
| provider env clone の小改善 | lookup 数が 462 / 1785 程度なら本丸じゃない                              |
| marker resume cache     | dynamic marker stack と hygiene baseline 依存で invalidation が重い |
| HashMap lookup cache    | route lookup より continuation machinery が大きい                  |
| Rc clone 削減だけ           | request append / marker resume の構造が残る                        |
| rope continuation だけ    | request 数と marker scope 処理が残る                                |

## 危ない

| 案                                                        | 危ない理由                                     |
| -------------------------------------------------------- | ----------------------------------------- |
| same-family handler を global に direct call               | callback hygiene を壊す                      |
| `HygieneFallback` を provider env で突破                     | blocked route の意味を変える                     |
| `delayed_boundary` を direct-tail 扱い                      | 捕捉境界の順序が変わる                               |
| marker frame をただ消す                                       | callback 由来 value/effect が外側 handler に漏れる |
| provider grant を scope/baseline なしで cache                | 古い handler token を再利用する事故                 |
| continuation tail を marker/provider frame の内側へ勝手に append | dynamic scope が変わる。今の code もそこは明示的に避けている。 |

---

# 8. 低リスク順の実装順

## Step 0: stats を増やす

まずここ。挙動は変えない。

追加する stats:

```text
provider_route_hits
provider_route_hit_direct_abortive
provider_route_hit_direct_tail
provider_route_hit_yield_fallback
provider_route_gate_fail_no_scope
provider_route_gate_fail_handler_shadow
provider_route_gate_fail_add_id_shadow
provider_route_gate_fail_request_boundary
effect_thunk_allocs
effect_apply_force_fusable
marker_resume_nonempty
marker_resume_empty
```

**期待効果:** 速度改善はなし。ただし次の一手の精度が上がる。
**リスク:** 低い。
**検証:** `compare.control: match`、既存 stats の増分だけ確認。

---

## Step 1: EffectOp apply + force の fuse

今は `EffectOp` に引数を apply すると `Thunk::Effect` を作り、あとで force する。 直後に force される形が plan で分かるなら、`RuntimeEvidenceExpr::EffectCall` に畳む。

```rust
RuntimeEvidenceExpr::EffectCall {
    site,
    callee,
    path,
    arg,
    target_value_is_thunk,
}
```

ただし effect thunk が値として渡るケースは現行通り。

**期待効果:** 小〜中。5〜15% くらいの余地。
**リスク:** 低〜中。thunk が観測可能な場合だけ注意。
**必要情報:** immediate force か、effect thunk が escape しない証明。
**検証:** effect op を thunk として保存するテスト、force 順序テスト、`compare.control: match`。

---

## Step 2: provider env を Vec/SmallVec slot table 化

今の `RuntimeEvidenceProviderEnv` は `Vec<RuntimeEvidenceEnvProvider>` で、`provides` が linear scan だねぇ。 slot 数が小さいなら SmallVec、slot id が密なら fixed vec / bitset がよさそう。

```rust
struct RuntimeEvidenceProviderEnv {
    dense: SmallVec<[(u32, SmallVec<[u32; 2]>); 4]>,
}
```

または plan 全体で slot id が小さいなら:

```rust
Vec<Option<SmallVec<[HandlerId; 2]>>>
```

**期待効果:** 小〜中。provider lookup が多い showcase では効くかも。
**リスク:** 低い。
**必要情報:** slot 数分布、candidate 数分布。
**検証:** provider lookup unit test、closure capture test、adapter provider env test。

---

## Step 3: provider grant gate の fail reason 化 + epoch 化

`provider_grant_path_gate_passes` は baseline 以降の add-id / handler frame を見る。 ここを epoch 化する。

```rust
struct ScopeEpochs {
    global_marker_epoch: u32,
    handler_epoch_by_path: PathEpochTable,
    add_id_epoch_by_path: PathEpochTable,
}
```

grant 作成時に snapshot。

```rust
Grant {
    handler_epoch,
    add_id_epoch,
    marker_epoch,
}
```

force 時に O(1) 比較。

**期待効果:** 小〜中。ただし fast path の土台として重要。
**リスク:** 中。path prefix と foreign-path marker が難所。
**必要情報:** path id、prefix relation table、marker policy。
**検証:** callback hygiene、foreign path marker、nested handler shadow、same-family nested handler。

---

## Step 4: evidence-direct route count を追加

`plan_direct_effect_routes` はそのまま残す。新しくこれを足す。

```text
plan_evidence_direct_candidates
runtime_evidence_direct_hits
runtime_evidence_direct_request_free_hits
runtime_evidence_direct_request_fallbacks
```

この段階では速度を変えず、分類だけ出す。

**期待効果:** 速度改善なし。でも判断が一気に楽になる。
**リスク:** 低い。
**検証:** synthetic provider route test、nondet/showcase stats regression。

---

## Step 5: abortive request-free fast path

resumptive より abortive が安全。continuation を持たないから marker resume の話が少ない。

条件:

```text
route = EvidenceDirect
arm_class = Abortive
grant gate passes
not HygieneFallback
not delayed boundary
payload marker empty or marked directly
```

**期待効果:** workload 次第。abortive handler が多いなら大。
**リスク:** 中。payload marker と handler visibility に注意。
**検証:** abortive handler、nested handler、callback boundary、guarded handler。

---

## Step 6: tail-resumptive request-free fast path

ここが本命。

条件:

```text
route = EvidenceDirect
arm_class = TailResumptive
grant path gate passes
continuation segment has no request boundary until target handler
resume marker policy is empty or explicitly handled
```

今の direct-tail machinery はすでに `continue_direct_tail_resumptive_with_continuation` にある。continuation に request boundary がなければ direct-tail append へ進む構造だねぇ。

ただし現状は append 先も continuation frame なので、次の Step 7 と合わせると効きやすい。

**期待効果:** 大。nondet みたいな resume-heavy workload の本命。
**リスク:** 高め。
**検証:** nondet、multi-shot では fallback、one-shot、tail resume、handler shadow、callback hygiene。

---

## Step 7: one-shot owned continuation stack

`DirectTailResumptive` の continuation だけでも owned stack にする。

```rust
struct DirectTailCall {
    handler: ExprId,
    payload: SharedValue,
    cont: OwnedContStack,
    hygiene: DirectHygieneState,
}
```

`EvidenceContinuation::Frame(Rc<...>)` へ入るのは、continuation が値として捕捉されるときだけ。

**期待効果:** 中〜大。request-free と合わせるとかなり効く。
**リスク:** 中。multi-shot / continuation escape の切替が肝。
**検証:** continuation を値として返す、複数回 resume、marked continuation call。

---

## Step 8: Koka 的 hidden evidence parameter

ここから設計変更が大きい。

* function signature に hidden evidence slots
* call site が evidence cells を渡す
* closure が provider env ではなく evidence cells を保持
* callback boundary で evidence cell を guard/drop
* effect op は local evidence cell を読む

**期待効果:** 大。provider lookup と env stack をかなり消せる。
**リスク:** 高い。compiler plan と runtime の両方に入る。
**検証:** full CLI suite、control VM comparison、callback hygiene golden tests、bench snapshot。

---

# 私なら最初に切る slice

一発目はこれがいいと思うよ〜。

```text
1. stats: provider route hit execution / gate fail reason を追加
2. immediate ForceThunk(Apply(EffectOp, arg)) fuse
3. provider grant gate を epoch 化する下準備
4. evidence-direct route category を stats に出す
5. tail-resumptive fast path は「marker-free 証明あり」のケースだけ有効化
```

特に `direct route を増やす` という言い方は少し危ない。増やすべきなのは static direct じゃなくて、**hygiene 証明つき evidence-direct** だねぇ。

一番避けたいのは、`plan_direct_effect_routes` を増やすために `LexicalHandlerCandidate` や `HygieneFallback` を雑に `DirectHandlerCall` 扱いすること。そこは速くなる前に意味論が壊れる可能性が高い。
逆に、provider grant / baseline / path epoch を証拠として持たせた direct fast path なら、control VM 互換を守りながら太い request machinery をかなり避けられると思うよ〜。
