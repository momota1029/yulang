うん、これは Codex に怒っていいやつだねぇ。
「Koka方式のVM」って頼んで `controlVM` の形をなぞるだけなら、それは**方式を変えたんじゃなくて、遅い抽象を別名で再実装しただけ**だよ〜。

## 結論

速い実装を手に入れるには、Codex への依頼をこう変えるのがよさそうだねぇ。

> **“Koka方式のVMを書け” ではなく、
> “この benchmark をこの counter で見て、この request / continuation 経路を 1 個だけ消せ” と頼む。**

今の evidence VM はすでに `RuntimeEvidenceThunk::Effect`、`EvidenceContinuation`、`EvidenceRequest`、`DirectTailResumptive` みたいな独自構造を持っている。だから「VMを作る」段階ではなく、**generic request machinery を通る回数を減らす**段階にいると思うよ〜。`RuntimeEvidenceThunk::Effect` は effect thunk に `route` と `evidence` を持たせていて、`EffectOp` apply 時には thunk を作り、force 時に `DirectAbortive` / `DirectTailResumptive` / `RoutedYield` / `Request` へ分岐している。

そしてボトルネック候補は、provider lookup そのものより、**effect thunk 作成、force、request 作成、continuation append、marker frame、catch body 再突入**の合成っぽい。stats もその観測をするための欄がかなり用意されている。

## まず Codex にやらせるべきじゃないこと

これは明確に止めた方がいいよ〜。

1. **`controlVM` の構造コピー**
2. **`request_free_yield = true` を雑に広げる**
3. **`HygieneFallback` や provider-env route を static direct 扱いする**
4. **`nondet::list` 専用 opcode で数字だけ作る**
5. **「Koka-style」と言いながら provider env stack lookup のままにする**

特に provider-env 由来 route は、ただの `handler: ExprId` じゃ足りない。今の design note にも、provider-env route は handler への直通ポインタだけではなく、grant の由来、scope、hygiene、call evidence を持つ必要があると整理されている。

## 「Koka方式」の実体を短く言うと

Koka 自体は row-polymorphic effect types を軸に effect を型へ出す言語で、効果を単なるタグではなく意味論とつなげる、という立場だねぇ。([arXiv][1])

でも、Yulang で速くしたい文脈では、たぶん欲しいのはこういうやつ。

```text
今:
  effect call
    -> active provider env stack を見る
    -> provider route lookup
    -> request / continuation machinery に落ちる

欲しい:
  function(hidden evidence cells..., normal args...)
    -> effect call は local evidence cell を読む
    -> hygiene gate が通るなら handler arm へ direct call
    -> generic request は fallback だけ
```

Yulang の note でも、Koka寄せなら lookup stack より hidden evidence parameter に寄せ、関数呼び出しが evidence slot を hidden arg として渡し、closure が provider env ではなく evidence cells を持つ方向が書かれている。

つまり Codex に渡すべき言葉は **“Koka方式VM”** じゃなくて、**“hidden evidence cell passing + request-free fast path”** だねぇ。

## 一発で速くしたいなら、最初の slice はこれ

私なら、次の順で切る。

### 1. まず stats を増やす

いきなり最適化しない。まず「どこで request path に落ちたか」を数える。

追加したい counter:

```text
provider_route_hit_direct_abortive
provider_route_hit_direct_tail
provider_route_hit_yield_fallback

provider_gate_fail_no_origin
provider_gate_fail_missing_scope
provider_gate_fail_hygiene_baseline
provider_gate_fail_add_id_shadow
provider_gate_fail_handler_shadow

effect_thunk_allocs
effect_thunk_immediate_force
effect_thunk_escaped

routed_yield_to_request_fallbacks
direct_tail_request_boundary_fallbacks
```

今の code は provider route lookup と hit 数までは持っているけど、hit の中身や gate fail reason がまだ粗い。`effect_route_for_operation_call` は static route を見て、なければ active provider env から `provider_route_for_call` を呼ぶ構造だよ〜。

### 2. `EffectOp apply → Thunk::Effect → force` を fuse する

今は `EffectOp` に引数を apply すると、まず `RuntimeEvidenceThunk::Effect` を作っている。
その後 force で route を見て `DirectTailResumptive` や `Request` へ分岐する。

ここを、escape しない形だけ:

```text
ForceThunk(Apply(EffectOp, arg))
```

から

```rust
RuntimeEvidenceExpr::EffectCall {
    site,
    effect_expr,
    path,
    arg,
}
```

みたいに畳む。

これは巨大な勝ちではないけど、Codex に最初にやらせるにはかなり良い。理由は、**意味論をほぼ変えずに、thunk allocation と force dispatch を消せる**から。

### 3. provider grant を「direct の証拠」に昇格する

今の `EvidenceProviderGrant` には `demand_slot_id`、`provider_slot_id`、`handler_id`、`scope_id`、`hygiene_baseline` が入っている。
provider frame 側も `scope_id` と hygiene baseline を持っていて、baseline が一致するかを見る実装がある。

だから次は、provider route を単なる lookup result じゃなくて:

```rust
EvidenceDirect {
    handler,
    handler_id,
    demand_slot_id,
    provider_slot_id,
    scope_id,
    hygiene_baseline,
    execution,
}
```

として扱う。
ここで gate が通る場合だけ request-free にする。

これは design note の方向とも一致する。`DirectHandlerCall` だけを direct と数えるのではなく、evidence grant 付き provider route を「hygiene 証明済み direct route」として扱う層を追加する、という整理が既にある。

### 4. tail-resumptive を request-free にする

20×20 nondet で効く本命はここだと思う。

今の direct-tail machinery はすでにある。`continue_direct_tail_resumptive_with_continuation` は request boundary がなければ continuation を direct-tail 側へ append する構造になっている。

でも provider route が request-free fast path に乗らなければ、結局 `Request` へ戻る。
なので条件付きで:

```text
route = EvidenceDirect
arm_class = TailResumptive
grant gate passes
no handler shadow
no add-id shadow
no request boundary
resume marker policy is empty or explicitly handled
```

のときだけ `DirectTailResumptive` に落とす。

design note でも tail-resumptive request-free fast path が resume-heavy workload の本命だと整理されている。

### 5. 20×20 nondet の本命は `Yield fragments`

ここが一番大事。

`nondet::branch` が `MayYield` / multi-shot 側なら、direct-tail だけでは 1ms 台には遠いかも。20×20 は、単に handler lookup が遅いんじゃなくて、**multi-shot continuation を毎回 request tree / continuation tree として組み直している**のが重いはずだねぇ。

note でも、20×20 を 7ms 近辺へ近づける次手は provider directization 単体ではなく、`Yield` representation と continuation fragments だと書かれている。

欲しい形はこう。

```rust
struct YieldContinuation {
    fragments: SmallVec<[ContinuationFragment; 8]>,
    shared_prefix: Option<ContinuationPrefixId>,
    resume_env: EvidenceEnvId,
    hygiene_resume_plan: MarkerPlanId,
    multi_shot: bool,
}
```

つまり `Request { continuation: EvidenceContinuation }` を毎回作るんじゃなくて、yield が泡みたいに上がる途中で **fragment を積む**。multi-shot のときだけ prefix を共有する。

## Codex に貼るなら、この依頼文がいい

```text
Task: Make evidence-vm faster without copying control-vm.

Repository: momota1029/yulang

Do not rewrite the VM wholesale.
Do not copy crates/control-vm runtime structure.
Do not add a nondet/list special case.
Do not set request_free_yield=true for provider-env routes unless a ProviderGrant gate proves it safe.
Do not treat HygieneFallback or delayed boundary as DirectHandlerCall.

Goal:
Reduce runtime overhead for the 20x20 nondet benchmark by removing one measured generic-request path, while preserving control VM comparison.

Read first:
- crates/evidence-vm/src/runtime.rs
- crates/evidence-vm/src/plan.rs
- notes/design/2026-06-28-evidence-vm-performance-pro-review.md
- notes/design/2026-06-28-provider-evidence-direct-yield-pro-review.md

Slice A:
1. Add stats counters:
   - provider_route_hit_direct_abortive
   - provider_route_hit_direct_tail
   - provider_route_hit_yield_fallback
   - provider_gate_fail_no_origin
   - provider_gate_fail_missing_scope
   - provider_gate_fail_hygiene_baseline
   - provider_gate_fail_add_id_shadow
   - provider_gate_fail_handler_shadow
   - effect_thunk_allocs
   - effect_thunk_immediate_force
   - effect_thunk_escaped
   - direct_tail_request_boundary_fallbacks

2. Do not change semantics in this step.
   All existing tests must pass.
   The benchmark output must still compare equal to control VM.

Slice B:
3. Add a planner/runtime fast path for immediate:
      ForceThunk(Apply(EffectOp, arg))
   lowering to:
      RuntimeEvidenceExpr::EffectCall { site, effect_expr, path, arg }
   only when the effect thunk does not escape.

4. Preserve current thunk behavior for all escaping effect thunks.

Acceptance:
- cargo fmt --check
- timeout 120s cargo test -q -p evidence-vm -p yulang -- --test-threads=1
- benchmark report includes before/after:
  - runtime_execute
  - effect_thunk_allocs
  - effect_thunk_immediate_force
  - request_continuation_appends
  - continuation_resume_steps
  - runtime_provider_env_route_hits

Expected:
- No semantic changes.
- Some reduction in effect thunk allocation / force dispatch.
- If benchmark does not improve, explain which counter shows the remaining bottleneck.
```

この依頼なら、Codex が「VMを書き直した風の巨大 diff」を出しにくい。
しかも、失敗しても counter が残るから、次の一手が見える。

## もっと強い依頼文: evidence-direct 版

最初の slice が通ったあとなら、次はこれ。

```text
Task: Add evidence-direct route classification, but do not enable request-free execution yet.

Goal:
Distinguish static DirectHandlerCall from provider-grant direct candidates.

Add:
- EvidenceDirect route category or RuntimeRouteCert
- stats:
  - plan_static_direct_effect_routes
  - plan_evidence_direct_candidates
  - runtime_evidence_direct_hits
  - runtime_evidence_direct_request_free_hits
  - runtime_evidence_direct_request_fallbacks

Rules:
- StaticDirect keeps current behavior.
- ProviderGrant route stores:
  - demand_slot_id
  - provider_slot_id
  - handler_id
  - scope_id
  - hygiene_baseline
  - execution plan
- ProviderGrant routes still fall back to current request path unless gate passes.
- No behavior change in this PR unless a separate test proves safety.

Add unit/golden tests:
- provider route survives returned effect thunk
- nested same-family handler shadow blocks grant
- callback hygiene blocks grant
- delayed boundary blocks grant
- control VM comparison remains equal
```

これでようやく「Koka方式っぽい」土台に入る。
今の design note でも、provider-env route を request-free にするなら `ProviderGrant` と `EffectThunkEvidence` を入れた後が安全、と整理されている。

## 目標値の置き方

「20×20 nondet を 1ms未満」は、今すぐの VM 改修目標としてはちょっと危険だと思う。
pure loop と同じ土俵に置くと、Codex が専用 opcode や意味論破壊に逃げる。

置くならこう。

```text
Phase 1: 35ms -> 28ms
  EffectOp apply/force fuse
  stats 完備

Phase 2: 28ms -> 18〜22ms
  evidence-direct route classification
  safe provider grant gate

Phase 3: 18〜12ms
  tail-resumptive request-free fast path
  marker-free 条件あり

Phase 4: 12ms -> 7ms 近辺
  Yield fragments
  prefix sharing
  multi-shot continuation snapshot

Phase 5: 7ms -> 低ミリ秒
  hidden evidence cells
  direct-style island
  generic request fallback を冷パス化
```

「1ms未満」を狙うなら、たぶん interpreter のままではきつくて、**nondet/list の意味を preserved した specialized lowering**、または **direct-style island + bytecode/stack VM** まで行く必要があると思うよ〜。ただし専用 opcode で数字だけ作るのは、言語処理系としては負け筋。

## 私なら、Codex の成果物をこう判定する

### 即 reject

```text
- archive/control-vm を大量に参照している
- crates/control-vm の型をさらに runtime hot path に増やしている
- request_free_yield を true に広げている
- HygieneFallback を Direct 扱いしている
- bench 専用条件が入っている
- stats が増えていない
- before/after の runtime_execute がない
```

### accept してよさそう

```text
- diff が小さい
- counter が増えている
- まず意味論変更なし
- control VM comparison が通る
- request / continuation / thunk のどれを減らしたか数字で言える
- 速くならなくても次の bottleneck が見える
```

## いちばん短い答え

早い実装を手に入れる道はこれだねぇ。

**Codex に「Koka方式のVM」を頼まない。**
代わりに、**“controlVM copy 禁止、bench と counter 必須、1 slice だけ、request path を何回消したか報告”** で縛る。

そして設計の軸はこれ。

```text
provider env lookup VM
  ↓
ProviderGrant / EffectThunkEvidence
  ↓
evidence-direct route
  ↓
tail-resumptive request-free fast path
  ↓
Yield fragments + prefix sharing
  ↓
hidden evidence cell passing
```

今の 35ms は「失敗」ではあるけど、まだ直せる失敗だと思うよ〜。ただし、次に Codex へ投げるときは **“VMを書け” じゃなく “この hot path をこの条件で消せ”** にしないと、また格好だけの巨大コピーが出てくる可能性が高い。

[1]: https://arxiv.org/abs/1406.2061?utm_source=chatgpt.com "Koka: Programming with Row Polymorphic Effect Types"
