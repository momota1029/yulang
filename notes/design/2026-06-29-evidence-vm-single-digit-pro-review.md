## 結論

次に一番筋がいいのは、**`MarkerFrame` / `ProviderEnv` を continuation frame として積む表現をやめて、`DirectTail` の resume continuation だけでも `EvalContSegment + ScopeDelta` に分けること**だと思うよ〜。

今の Evidence VM は、意味論はかなり evidence-native になっているけど、実行表現はまだ **request / marker / provider / continuation が同じ tree に混ざった machine** に近い。実装でも `EvidenceContinuationFrame` の中に `Then`、通常 frame、`MarkerFrame`、`ProviderEnv` が同居しているし、ProviderEnv close は signal の continuation に `ProviderEnv` frame を追加する形だねぇ。

`bench/nondet_20_discard.yu` は `each 1..20 + each 1..20` の結果を `.list` で集めて捨てる workload で、`nondet.list` は `branch(), k -> merge k(true).list k(false).list` という典型的な resumptive fork 形になっている。だから `k true` / `k false` の両側で、ほぼ同じ marker/provider continuation shape を何度も再構成する圧が出る。

---

## ランキング

|  Rank | 方向                                                                    | 期待 speedup | semantic risk | 実装サイズ | validation しやすさ |
| ----: | --------------------------------------------------------------------- | ---------: | ------------: | ----: | --------------: |
| **1** | **`DirectTail` 用 `EvalContSegment + ScopeDelta`**                     |      **大** |           中〜高 |     中 |               高 |
| **2** | **`ResumeMarkerPlanId` + marker enter-op precompute**                 |        中〜大 |             中 |   小〜中 |               高 |
| **3** | **`RouteCert` / evidence-direct route surface の first-class 化**       |          中 |             中 |     中 |               高 |
| **4** | **resumptive fork pack: `k true` / `k false` が同じ frozen segment を共有** |        中〜大 |             高 |     中 |               中 |
| **5** | **lowering/mono が specialized runtime evidence surface を出す**          |          大 |             高 |     大 |               中 |
| **6** | `std.control.nondet.list` builder / collector                         |        小〜中 |           低〜中 |   小〜中 |               高 |
| **7** | env clone / thunk force / primitive list merge の個別削減                  |        小〜中 |             低 |     小 |               高 |

私なら **1 → 2 → 3 → 4** の順で切るねぇ。`nondet_20_discard` を 10.5〜12.1ms から安定一桁へ落とすには、1 か 2 のどちらか単独、あるいは 1+2 の合わせ技が必要そう。現状の最終測定は nondet が 10.5〜12.1ms、showcase が 24〜26ms、どちらも `compare.control: match` だねぇ。

---

## 1. 本命: `DirectTail` continuation を segment + scope delta にする

### 何を変えるか

今:

```text
DirectTailResumptive {
  continuation: EvidenceContinuation
}

EvidenceContinuation =
  Then(...)
  MarkerFrame(...)
  ProviderEnv(...)
  Apply/Force/Case/Block...
```

次:

```rust
struct DirectTailCall {
    handler: ExprId,
    payload: SharedValue,
    resume_segment: EvalContSegment,
    scope_delta: ScopeDelta,
    cert: RouteCertId,
}

struct EvalContSegment {
    frames: SmallVec<[EvalFrame; 8]>,
    shared_prefix: Option<ContPrefixId>,
    multiplicity: ContinuationMultiplicity,
}

struct ScopeDelta {
    resume_marker_plan: ResumeMarkerPlanId,
    provider_env_delta: Option<ProviderEnvDeltaId>,
    handler_boundary: Option<HandlerBoundaryId>,
}
```

ポイントは、**marker/provider scope を消すんじゃなく、continuation tree から追い出す**こと。`MarkerFrame` と `ProviderEnv` が tail append の境界になって `Then` が増える現状は、意味論上の正しさの副作用だよ〜。だから境界を無視して flatten するんじゃなく、`ScopeDelta` として別レーンへ持つ。

この方向は既存 design note の見立てとも一致している。そこでも marker/provider を continuation frame から外し、`ScopeDelta` / `MarkerPlanId` / `ProviderScopeToken` として segment に付ける案が中心に置かれている。

### soundness invariant

`EvalContSegment` は **ordinary eval frame だけ**を含む。`MarkerFrame` / `ProviderEnv` / handler boundary / AddId activation は `ScopeDelta` 側に移す。

必要 invariant はこれ:

```text
resume(segment, scope_delta, value)
≡
resume_continuation(
  close_provider_env(
    close_marker_frame(segment_as_tree, scope_delta.marker_plan),
    scope_delta.provider_env
  ),
  value
)
```

ただし `scope_delta` は次を持つ:

```text
- resume 中に activate すべき AddId enter ops
- value payload に付ける marker slice
- handler boundary exposure
- provider scope token
- provider hygiene baseline
- continuation multiplicity
```

`carry_after_frame == false` を「resume 中も不要」と読んだら壊れる。design note でも、`markers_for_continuation_resume` が空でないのに marker frame を単に消すと callback 由来 effect が外側 handler に漏れる、と警告されている。

### 動くべき counters

方向が正しければ、まずここが落ちるはず:

```text
continuation_resume_steps
continuation_resume_then_steps
continuation_resume_marker_steps
continuation_resume_force_steps
marker_frame_continuation_resume_entries
direct_tail_continuation_then_appends
continuation_append_blocked_by_marker_frame
continuation_append_blocked_by_provider_env
provider_env_then_compaction_provider_env_then_first
```

逆に、`expr_evals` は最初そこまで落ちなくてもいい。構造改善の初期シグナルは **resume / Then / marker/provider scope** の counters に出るはず。

### 最初の小さい patch

速度を狙わずに、まず backend を増やすだけがいいよ〜。

```rust
enum DirectTailContinuation {
    Tree(EvidenceContinuation),
    Segment {
        segment: EvalContSegment,
        scope_delta: ScopeDelta,
    },
}
```

最初は `Segment` を作っても、resume 直前に `to_tree()` で現行 path へ戻す。追加 stats:

```text
direct_tail_segment_candidates
direct_tail_segment_created
direct_tail_segment_to_tree_fallbacks
direct_tail_segment_scope_marker_dynamic
direct_tail_segment_scope_marker_empty
direct_tail_segment_scope_provider_env
direct_tail_segment_multi_shot_rejected
direct_tail_segment_request_boundary_rejected
```

これで `compare-control` を一切揺らさず、「どれくらい segment 化できるか」だけ見る。

### falsify 条件

この方向が外れなら、こう出る:

```text
direct_tail_segment_candidates が少ない
segment_to_tree_fallbacks が候補の大半
request_boundary_rejected が支配的
multi_shot_rejected が支配的
segment 化しても continuation_resume_steps / Then がほぼ不変
```

逆に `segment_created` が多く、`Then` と marker resume が落ちるなら本命継続。

---

## 2. `ResumeMarkerPlanId` + marker enter-op precompute

### 何を変えるか

今の `resume_marker_frame` は、resume 時に marker frame を再 push し、active marker plan も push して、その中で `resume_continuation` する形だねぇ。

これを段階的にこうする:

```rust
enum ResumeMarkerPlan {
    Empty,

    PureValueMark {
        markers: MarkerSliceId,
        type_filter: TypeMarkPolicy,
    },

    DynamicScope {
        enter_ops: SmallVec<[MarkerEnterOp; 4]>,
        value_mark: MarkerSliceId,
        handler_boundary: Option<HandlerBoundaryPlanId>,
    },
}
```

最初は `Rc<[EvidenceValueMarker]>` を intern して `RuntimeMarkerPlanId` を作るだけ。意味は変えない。次に `DynamicScope` の enter ops を precompute して、resume のたびに marker vector 全体を走査しない。最後に `PureValueMark` の場合だけ push/pop を省く。

### soundness invariant

`PureValueMark` に落としていい条件はかなり狭い:

```text
- resume 中に active AddId が必要ない
- handler_path がない
- carried guard / resume delta がない
- provider permission visibility を変えない
- 値 payload marking だけで legacy close と同じ
```

それ以外は `DynamicScope`。ここを欲張ると hygiene が壊れる。

### 動くべき counters

```text
marker_frame_entries
marker_frame_markers
marker_frame_active_add_id_markers
active_marker_plan_pushes
active_marker_plan_dedupes
active_add_id_scans
marker_frame_continuation_resume_entries
```

ただし、以前の duplicate marker scope skip は `marker_frame_entries` を 13526 → 7293 まで減らしても実時間は悪化した。だから **entries が減るだけでは合格にしない**。`active_add_id_scans`、enter-op count、close shape、実時間まで一緒に見る必要がある。

### 最初の小さい patch

```text
1. marker slice interning
2. ResumeMarkerPlan 分類だけ追加
3. 全 execution は現行と同じ push/pop
4. stats だけ見る
```

追加 stats:

```text
resume_marker_plan_empty
resume_marker_plan_pure_value
resume_marker_plan_dynamic_scope
resume_marker_plan_enter_ops_total
resume_marker_plan_handler_boundary
resume_marker_plan_active_add_id_ops
resume_marker_plan_to_legacy_push_pop
```

### falsify 条件

```text
pure_value がほぼ 0
dynamic_scope の enter_ops が現行 marker 走査と同じくらい重い
active AddId / handler boundary が支配的
runtime が marker entries 減少に反応しない
```

この場合は、marker plan 単独より rank 1 の segment 化へ戻る方がいい。

---

## 3. `RouteCert` / evidence-direct route surface

### 何を変えるか

今の plan は `DirectHandlerCall` だけ static direct route にして、`LexicalHandlerCandidate` / `HygieneFallback` / `GenericFallback` は static route では `Unhandled` にする。

一方で provider lookup はすでに runtime にあり、active provider env から route と provider grant origin を返す。 ただし provider route 側の `EvidenceEffectRoute::Direct` は `request_free_yield: false` で作られている。

だから次は `request_free_yield: bool` だけで扱うんじゃなく、こういう証明オブジェクトに寄せる:

```rust
enum RouteCert {
    StaticDirect {
        handler: ExprId,
        execution: HandlerExecution,
    },

    ProviderGrant {
        handler: ExprId,
        handler_id: u32,
        demand_slot_id: u32,
        provider_slot_id: u32,
        scope_id: EvidenceProviderScopeId,
        hygiene_baseline: EvidenceProviderHygieneBaseline,
        execution: HandlerExecution,
    },

    Fallback,
}
```

既存の `EffectThunkEvidence`、`EvidenceRouteCert`、`EvidenceProviderGrant` は足場としてかなり近い。`RuntimeEvidenceThunk::Effect` は route と evidence をすでに保持している。

### soundness invariant

ProviderGrant direct 化の条件:

```text
- scope_id が active
- hygiene_baseline 以降に同 path handler shadow がない
- hygiene_baseline 以降に relevant AddId shadow がない
- delayed boundary ではない
- HygieneFallback ではない
- handler definition env が正しい
- operation family と permission family が一致
- request boundary を越えない
```

今の direct-tail gate は provider grant の scope と baseline を見て、handler shadow / AddId shadow を検査している。ここを route cert の正式 invariant に昇格するのが筋だねぇ。

### 動くべき counters

```text
runtime_provider_env_route_hits
runtime_provider_env_route_hit_direct_tail_resumptive
direct_tail_gate_fail_*
yield_signal_direct_provider
yield_signal_to_request
runtime_evidence_direct_request_free_hits
runtime_evidence_direct_request_fallbacks
```

現状すでに provider route hit 分解 counter は入っているので、ここは validation しやすい。`effect_route_for_operation_call` も static route → provider lookup → provider hit stats という順で動く。

### 最初の小さい patch

`RouteCert` を入れるが、挙動は変えない。

```text
StaticDirect => 旧 request_free_yield true
ProviderGrant => 旧 request_free_yield false
Fallback => 旧 Unhandled
```

追加 stats:

```text
route_cert_static_direct
route_cert_provider_grant
route_cert_provider_grant_clean
route_cert_provider_grant_dirty_scope
route_cert_provider_grant_dirty_add_id
route_cert_provider_grant_dirty_handler
route_cert_to_request_free
route_cert_to_legacy_request
```

### falsify 条件

```text
provider_grant_clean が少ない
dirty_add_id / dirty_handler が支配的
ProviderGrant direct を有効化しても request / marker counters が動かない
```

この場合、route 証明だけでは足りず、rank 1 の continuation 表現が先。

---

## 4. `k true` / `k false` の shape 再構築を避ける fork pack

### 何を変えるか

`nondet.list` の hot pattern はこれ:

```text
branch(), k -> merge k(true).list k(false).list
```

安全にやるなら、`branch` 専用 hack ではなく、**resumptive continuation の frozen pack** として一般化する。

```rust
struct ResumePack {
    segment: EvalContSegment,
    scope_delta: ScopeDelta,
    multiplicity: ContinuationMultiplicity,
    cert: RouteCertId,
}

fn resume_pack(pack: &ResumePack, arg: SharedValue) -> EvidenceEvalResult
```

`branch` handler は `k` を受け取った時点で `ResumePack` を作り、`true` と `false` の両方で同じ pack を使う。左右で value payload だけ違う。

### soundness invariant

```text
- pack は immutable / frozen
- multi-shot なら Shared segment
- one-shot なら一度だけ consume
- provider scope token は resume ごとに gate 再検査
- marker dynamic scope は ScopeDelta で復元
- handler boundary / AddId visibility は pack 作成時ではなく resume 時に有効
```

nondet は multi-shot 的に同じ continuation を左右で使うので、ここで `Owned` を雑に再利用すると壊れる。`ContinuationMultiplicity` を先に固定する必要がある。

### 動くべき counters

```text
thunk_force_continuation
continuation_resume_steps
continuation_resume_then_steps
marker_frame_continuation_resume_entries
env_clones
request_continuation_appends
list_merge_calls は大きくは変わらない可能性あり
```

### 最初の小さい patch

いきなり fuse しない。まず continuation thunk 作成時に pack candidate を数える:

```text
resume_pack_candidates
resume_pack_multi_shot_required
resume_pack_scope_dynamic
resume_pack_provider_delta
resume_pack_can_share_segment
resume_pack_rejected_escaped
```

### falsify 条件

```text
pack candidate が少ない
multi-shot shared 化コストが現行 clone/tree より重い
provider/marker scope がほぼ毎回 dynamic で pack reuse の効果が消える
```

---

## 5. lowering / mono はもっと specialized runtime surface を出すべきか

**出すべき。ただし今すぐ full bytecode 化は早い**、という見方だねぇ。

最初に lowering が出すべきもの:

```text
- RouteCert provenance
- operation execution class
- continuation multiplicity
- marker policy
- provider slot requirements
- callback / delayed boundary flag
- handler definition env
- direct-tail segment eligibility
```

いまの operation lowering は `DirectHandlerCall` / `LexicalHandlerCandidate` / `HygieneFallback` / `GenericFallback` を持っている。 これを runtime が毎回再発見するより、**runtime evidence surface に fast class と cert を出す**方が Koka-style evidence passing に近い。

でも、hidden evidence params まで一気に行くと compiler + runtime 両方が大きく動く。まずは `RouteCert` と `ScopeDelta` の surface 固定が先。

---

## 6. `std.control.nondet.list` は pathological か

半分 yes、半分 no。

yes な部分:

```text
branch(), k -> merge k(true).list k(false).list
```

これは DFS の左右それぞれで continuation resume + handler catch + marker/provider close を繰り返す。discard benchmark では最終 list を捨てるので、意味上は「集めた結果を捨てる」だけなのに、runtime は全部構築する。

no な部分:

`list_merge` 自体は `ListTree::concat` で、空なら即返し、非空同士は red-black tree 的に node を作る構造だねぇ。これは普通の linked list append よりだいぶマシ。 だから今すぐ list builder を本命にするより、resume/marker/provider の machinery を先に削る方が当たりそう。

### builder 案

標準ライブラリ側でやるなら:

```text
nondet.collect_with(builder, emit)
```

または runtime primitive 側に:

```rust
ListBuilder {
    chunks: SmallVec<[ListTree<SharedValue>; 8]>,
}
```

を置き、`v -> builder.push(v)`、最後に `ListTree::from_items` または balanced concat で確定する。

result order は今の `.list` と同じく:

```text
true branch results, then false branch results
```

を守る。これなら handler semantics は保てる。

ただし、`nondet_20_discard` 専用に「`.list` 結果が未使用なら消す」はやらない方がいい。path/name/test-specific branch になるし、effect の可観測性が絡む。

---

## 7. env_clones / thunk_forces / resume steps は同じ原因か

大枠では **同じ表現問題の症状**が多いと思うよ〜。

特に nondet では:

```text
thunk_force_continuation
continuation_resume_force_steps
marker_frame_continuation_resume_entries
provider_env frames under Then
```

が絡むので、continuation を値として force → tree resume → marker/provider 再入場、という流れが太い。

ただし `env_clones` は一部別問題。`ApplyCallee` / `CaseScrutinee` / `BlockStmt` など continuation frame が `Env` を持つので、tree frame が多いほど env clone 圧も上がる。`EvidenceContinuationFrame` の通常 frame 群も `env: Env` を保持している。

だから順番はこう:

```text
1. continuation / scope 表現を変える
2. それで env_clones がどれだけ自然減するか見る
3. 残った env clone だけ別に攻める
```

いきなり env clone だけ削ると、表現問題の影を追うだけになりやすい。

---

## profiler で最初に見る場所

### continuation representation cost

```text
EvidenceContinuation::then_counted
EvidenceContinuation::try_append_owned_tail_counted
EvidenceContinuationFrame::try_append_owned_tail_counted
EvidenceContinuationFrame::has_request_boundary
resume_continuation
```

見る event:

```text
Then allocation count
Rc::get_mut fail count
Rc clone count
append_scope_blocker: MarkerFrame / ProviderEnv / RcShared
resume frame dispatch count
```

### marker close cost

```text
with_marker_frame
resume_marker_frame
close_marker_frame_result
close_marker_direct_tail
push_marker_frame
pop_marker_frame
push_active_marker_plan
markers_for_function_call_shared
markers_for_continuation_resume
```

`resume_marker_frame` は push/pop してから `resume_continuation` し、その後 close するので、ここは flamegraph で太く出るはず。

### provider environment restoration cost

```text
with_provider_env
close_provider_env_result
close_provider_env_signal
active_provider_env_views
RuntimeEvidenceRunContext::provider_route_for_call
RuntimeEvidenceProviderEnv::provides
```

ProviderEnv 自体の lookup 数は大きすぎないが、ProviderEnv が continuation shape に混ざることが問題。`active_provider_env_views` は active frame を filter して view を作り、provider lookup に渡す。

### closure environment cloning cost

```text
Env::clone
apply_value
eval_expr_result
bind_pattern
RuntimeEvidenceClosure construction
RuntimeEvidenceThunk::Expr construction
EvidenceContinuationFrame::{ApplyCallee, CaseScrutinee, BlockStmt}
```

event:

```text
env_clones by caller
env_entries_cloned by caller
Env size histogram
closure env size histogram
```

### list construction / merge cost

```text
primitive_apply list_merge
ListTree::concat
ListTree::from_items
ListTree::view
ListTree::to_vec
```

event:

```text
list_merge_calls
list_values_copied
ListTree node allocations
ListTree black_height calls
```

`list_merge_calls: 420` は無視できないけど、nondet の主犯と見るにはまだ弱い。resume/marker/provider の counters が先に太すぎる。

---

## 「やらない方がいい」リスト

これはかなりはっきりしてるよ〜。

1. **later ProviderEnv grant native close の復活**
   可視性は合っても遅かった。notes でも、原因は close 条件ではなく placement 探索と continuation representation 側、と読まれている。

2. **nearest ProviderEnv miss を invisibility とみなす**
   これは invariant に反する。miss は invisibility の証明じゃない。

3. **any ProviderEnv presence を permission evidence にする**
   nearest grant / nearest miss / later grant は分離したまま扱うべき。

4. **`ProviderEnv(env, ProviderEnv(env, k))` collapse を次にやる**
   deep profile では exact same ProviderEnv candidate が nondet/showcase とも 0。adjacent ProviderEnv はあるが observed cases は different env だねぇ。

5. **duplicate marker scope skip の再挑戦を本命にする**
   marker frame 数は減ったが実時間は悪化済み。cover check と close shape が勝つ。

6. **`LexicalHandlerCandidate` / `HygieneFallback` を雑に `DirectHandlerCall` 扱い**
   callback hygiene を壊す可能性が高い。ProviderGrant direct 化は cert 経由でやるべき。

7. **`Then` / `ProviderEnv` flatten を scope invariant なしでやる**
   これは速く見えて dynamic scope を変えるやつ。

8. **LTO / target-cpu / stats removal を言語レベル解として数える**
   たまに 9.7ms が出ても平均が 10ms 台で、build cost も重い。

---

## 具体的な次 patch slice

私なら次の review にこう出すかなぁ。

```text
Patch A: DirectTail segment shadow
- DirectTail continuation candidate を segment として分類
- 実行は to_tree fallback
- stats 追加
- compare-control / adversarial probe 維持

Patch B: ResumeMarkerPlanId shadow
- marker slice intern
- Empty / PureValueMark / DynamicScope 分類
- 実行は現行 push/pop
- enter-op 数だけ測る

Patch C: RouteCert first-class
- StaticDirect / ProviderGrant / Fallback を明示
- request_free_yield はまだ旧挙動
- provider_grant_clean / dirty counters を出す

Patch D: DirectTail segment 実行を限定有効化
- request boundary なし
- marker plan DynamicScope は旧 path fallback
- provider env delta が単純な nearest grant/pair だけ
- multi-shot は Shared segment のみ
```

これで、`bench/nondet_20_discard.yu` の一桁化に必要な構造差分を、hygiene を弱めずに切り分けられると思うよ〜。最初から全部速くしようとせず、**Tree と Segment の二重 backend**で `compare-control` を握ったまま shadow stats を積むのが一番安全だねぇ。
