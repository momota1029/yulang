## 結論

一桁 ms を狙う本命は、**`CatchBody` / handler boundary / `MarkerFrame` / `ProviderEnv` を continuation frame から外して、ordinary eval frame と scope/evidence delta を別レーン化する structural rewrite** だねぇ。

以前の「`DirectTail` を `EvalContSegment + ScopeDelta` にする」案は方向として正しい。ただし、現 shadow profile では **eval-only segment では足りない** ことがもう見えている。`direct_tail_segment_candidates` は nondet で 420、showcase で 829 あるのに、`created: 0`、全件 `request_boundary_rejected`。つまり `CatchBody` が残る限り、単なる eval segment 化は入口で止まる。

だから次の rewrite はこういう形がよさそう。

```text
EvidenceContinuation tree
  = eval frame
  + CatchBody
  + MarkerFrame
  + ProviderEnv
  + Then
```

をやめて、

```text
ResumePlan {
  eval_segment: EvalSegment,
  handler_boundary_delta: HandlerBoundaryDelta,
  marker_delta: MarkerScopeDelta,
  provider_delta: ProviderScopeDelta,
  request_boundary_delta: RequestBoundaryDelta,
  multiplicity: one-shot | multi-shot,
  route_cert: RouteCert,
}
```

へ寄せる。
**scope を flatten するんじゃなく、scope を continuation spine から追い出す**、というのが大事だねぇ。

---

## 1. 一桁 ms の本命

本命は **`CatchBody-aware ResumePlan`** だと思うよ〜。

もう少し具体的には、`DirectTail` / continuation thunk / resume pack の materialization 時に、今の tree continuation をそのまま持たず、

```rust
struct ResumePlan {
    eval: EvalSegment,
    request: RequestBoundaryDelta,
    handler: HandlerBoundaryDelta,
    marker: MarkerDelta,
    provider: ProviderDelta,
    route: EvidenceRouteCert,
    multiplicity: ContinuationMultiplicity,
}
```

みたいな「resume 専用 IR」に落とす。

理由はかなり強い。

今の `EvidenceContinuationFrame` は、`Then`、ordinary eval frame、`CatchBody`、`MarkerFrame`、`ProviderEnv` が同じ enum に同居している。これは意味論的には堅いけど、resume 時には毎回 tree を歩く形になりやすい。

そして実測上、`DirectTail` segment 候補も resume pack 候補も多いのに、どちらも全件 request boundary に当たって share / segment 化が止まっている。resume pack は nondet で候補 840、全件 multi-shot、でも `resume_pack_can_share_segment: 0`、`resume_pack_request_boundary_rejected: 840`。showcase でも同じ傾向だねぇ。

つまり「continuation を segment 化する」は当たりだけど、**`CatchBody` を segment 外の blocker として扱う設計だと当たらない**。次は `CatchBody` 自体を `RequestBoundaryDelta` / `HandlerBoundaryDelta` として first-class 化する段階。

---

## 2. どれを分けるべきか

優先順位はこれ。

```text
1. CatchBody / request boundary
2. MarkerFrame
3. ProviderEnv
4. Env clone
```

### `CatchBody` は分けるべき

ここがいま一番の栓。
ただし **`CatchBody` を request boundary から外す** ではないよ〜。それは hygiene を壊す寄り。

現 profile では `CatchBody` は hot path で太い。nondet で `catch_boundary_entries: 2962`、`catch_boundary_direct_tail_signals: 861`、showcase で `catch_boundary_entries: 6577`、`catch_boundary_direct_tail_signals: 1791`。ただし `direct_tail_blocked_by_catch_boundary: 0` なので、「direct-tail が CatchBody に入れない」問題ではない。問題は、**resume/pack/segment の表現内に CatchBody が残り、共有や segment 化を阻害している**ことだねぇ。

だから `CatchBody` は ordinary frame ではなく、

```text
RequestBoundaryDelta {
  catch_expr,
  arms,
  handler route visibility,
  provider grant gate,
  fallback policy,
}
```

みたいに別管理するのが筋。

### `MarkerFrame` も分けるべき

でも `PureValueMark` 最適化は本命じゃない。
ResumeMarkerPlan shadow では nondet/showcase とも `pure_value: 0`、全部 `dynamic_scope`。active AddId も plan 数と同数出ている。

なので「marker push/pop を省く」ではなく、**dynamic enter-op を precompute して resume plan の一部にする**方向が良い。

```text
MarkerDelta {
  enter_ops: Interned<[MarkerEnterOp]>,
  active_add_id_ops: Interned<[AddIdEnterOp]>,
  handler_boundary_ops: Interned<[HandlerBoundaryEnterOp]>,
}
```

ここは `ResumeMarkerPlanId` の発展版だねぇ。

### `ProviderEnv` も分けるべき

`ProviderEnv` の exact collapse は今やる価値が薄い。deep profile で exact same ProviderEnv は nondet/showcase とも 0、adjacent はあるけど different env。

なので `ProviderEnv(env, ProviderEnv(env, k))` みたいな局所 rewrite じゃなく、

```text
ProviderDelta {
  scope_token,
  provider_env_ref,
  hygiene_baseline,
  nearest_grant/miss/later_grant classification,
}
```

として continuation tree から切り離す方がいい。

### `env clone` は最後

`env_clones` は多いけど、`env_entries_cloned` がほぼ 0 に近いなら、巨大 env copy ではなく **frame 構築・closure/thunk/resume 周辺で空/薄い env を何度も持ち回っている症状**に見える。
つまり `Env` だけ直すと影を追う形になりやすい。`EvalSegment` 側で ordinary frame を compact にしたあと、残った clone を caller 別に潰すのがよさそう。

---

## 3. Koka 的 evidence passing に近づけるなら、まず壊す抽象境界

壊すべき境界は **「effect request signal と evidence route / provider permission / handler boundary が別物として runtime tree 上を流れる」境界**だねぇ。

今はかなり evidence-native になっているけど、実行表現はまだ、

```text
effect occurs
→ signal / thunk / continuation
→ CatchBody / MarkerFrame / ProviderEnv を tree で通る
→ visibility / provider grant / handler hygiene を runtime で再判定
```

に近い。

Koka 的に寄せるなら、まず runtime の値として流れる effect/resume に、

```text
RouteCert
ProviderGrantGate
HandlerBoundaryDelta
MarkerDelta
ProviderDelta
```

を一体化して持たせたい。

`EvidenceRouteCert` 自体はもう入り始めているし、`EffectThunkEvidence` も `route_cert` と `visibility` を持っている。
ただ、現 profile だと provider grant は clean ではなく AddId dirty が支配的で、`route_cert_provider_grant_clean: 0`。だから `RouteCert` だけ first-class にしても request-free path は増えない。

なので、壊す境界は `RouteCert` 単体じゃなくて、

```text
RouteCert + AddId/handler/provider hygiene delta + CatchBody boundary
```

を別々に runtime が探す境界。

言い換えると、**「route は route、scope は continuation frame、hygiene は marker scan」になっている境界**を壊して、resume plan にまとめる。

---

## 4. native backend 前に VM 側でまだ大きく削れるか

あると思う。
ただし、小技じゃなくて **resume の IR 化** が必要。

削れそうな構造はこれ。

### A. continuation tree resume を `ResumePlan` 実行へ変える

狙う counter はここ。

```text
continuation_resume_steps
continuation_resume_then_steps
continuation_resume_catch_steps
continuation_resume_marker_steps
continuation_resume_force_steps
thunk_force_continuation
```

`expr_evals` も多いけど、いきなり expression evaluator 全体を bytecode 化するより、まず resumptive fork の resume path を切る方が当たりそう。

### B. `CatchBody` を ordinary frame から handler boundary delta に移す

これは一桁狙いの中心。

今の shadow から見ると、

```text
DirectTail segment: 候補あり、request boundary で全拒否
resume pack: 候補あり、request boundary で全拒否
CatchBody: hot だが direct-tail blocker ではない
```

という状態。だから `CatchBody` を消すんじゃなく、**resume plan の handler boundary として実行可能にする**必要がある。

### C. dynamic marker enter-op precompute

`PureValueMark` は 0 なので、push/pop 省略は刺さらない。
でも dynamic scope の enter-op 総数は nondet で 10057、showcase で 19671。ここは precompute / intern / compact op dispatch でまだ削れる余地がある。

### D. multi-shot resume pack は `CatchBody-aware` になってから

resume pack 候補は多い。nondet で 840、showcase で 1655。
でも全件 request boundary rejected で `can_share_segment: 0`。なので今すぐ pack reuse 実行へ行くと失敗しやすい。まず `CatchBody-aware ResumePlan` を作ってから、同じ plan を `k true` / `k false` で共有するのがよさそう。

---

## 5. 次にやるべきではない案

かなりはっきりしてる。

| 案                                                 | やらない理由                                            |
| ------------------------------------------------- | ------------------------------------------------- |
| later grant native close 復活                       | 速度面で不採用済み。placement 探索と continuation shape が主因寄り  |
| nearest ProviderEnv miss = invisibility           | invariant 違反。miss は不可視の証明じゃない                     |
| any ProviderEnv presence を permission evidence 扱い | nearest grant / miss / later grant の区別を壊す         |
| exact ProviderEnv collapse                        | exact same candidate が 0                          |
| duplicate marker scope skip 再挑戦                   | marker 数は減ったのに実時間悪化済み                             |
| `RouteCert` 単体で request-free 化                    | clean provider grant が 0、AddId dirty が支配的         |
| `PureValueMark` push/pop 省略                       | pure value plan が 0                               |
| path/string lookup 系                              | すでに支配項ではなさそう                                      |
| `CatchBody` を単純に boundary から外す                    | direct-tail blocker ではなく、handler hygiene を壊す危険が高い |
| native backend へ先に逃げる                             | VM 表現の無駄が残ったまま native 化することになる                    |

---

## 私なら次に切る patch

### Patch 1: `ResumePlan` shadow v1

実行は旧 tree のまま、分類だけ作る。

```rust
enum ResumePlanShadow {
    TreeOnly,
    Planned {
        eval_frames: usize,
        catch_boundaries: usize,
        marker_dynamic_ops: usize,
        provider_env_deltas: usize,
        route_cert: EvidenceRouteCert,
        multi_shot: bool,
    },
}
```

見る stats:

```text
resume_plan_candidates
resume_plan_with_catch_boundary
resume_plan_with_dynamic_marker
resume_plan_with_provider_delta
resume_plan_provider_grant_dirty_add_id
resume_plan_multi_shot
resume_plan_tree_equivalent
```

### Patch 2: `CatchBody` を `RequestBoundaryDelta` に分類

ここでも実行は旧 tree。

```rust
enum RequestBoundaryDelta {
    None,
    Catch {
        catch_expr: ExprId,
        handler_visibility: HandlerVisibilityPlan,
        provider_gate: Option<EvidenceProviderGrantGate>,
        fallback: CatchFallbackPolicy,
    },
    RefSet,
}
```

合格条件はこれ。

```text
direct_tail_segment_request_boundary_rejected が
  resume_plan_with_catch_boundary に吸収される

resume_pack_can_share_segment が 0 から増える
```

### Patch 3: dynamic marker enter-op intern

`PureValueMark` は捨てていい。全部 dynamic 前提で、

```rust
struct MarkerDeltaId(u32);

struct MarkerDelta {
    enter_ops: Rc<[MarkerEnterOp]>,
    active_add_id_ops: Rc<[AddIdEnterOp]>,
    handler_boundary_ops: Rc<[HandlerBoundaryEnterOp]>,
}
```

にする。

### Patch 4: `ResumePlan` 実行を限定有効化

最初の有効化条件は狭く。

```text
- compare-control shadow match 済み
- RequestBoundaryDelta::Catch の route が visible
- ProviderGrant dirty AddId を MarkerDelta で再現できる
- multi-shot は immutable ResumePlan のみ
- ProviderEnv / MarkerFrame scope boundary は tree flatten しない
```

---

## 最終判断

**「CatchBody / handler boundary / MarkerFrame / ProviderEnv を分ける」が答えだねぇ。**
ただし分け方は、`CatchBody` だけ、`MarkerFrame` だけ、`ProviderEnv` だけ、では弱い。

今のデータから見る本命はこれ。

```text
DirectTail / continuation thunk / resume pack 用に
CatchBody-aware ResumePlan を作る

ordinary eval frame は EvalSegment
CatchBody は RequestBoundaryDelta
MarkerFrame は MarkerDelta
ProviderEnv は ProviderDelta
RouteCert はその plan に同梱
```

これなら hygiene を守ったまま、tree resume / Then / marker/provider 再構成 / multi-shot pack 不成立のまとめて太い部分に当てられる。逆にここへ行かずに、RouteCert 単体、ProviderEnv collapse、pure marker skip、env clone 小技を続けるのは、もうだいぶ収穫逓減に入ってると思うよ〜。
