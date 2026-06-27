# Runtime evidence marker state Pro review

Date: 2026-06-27

Context:
- Runtime evidence runner performance work.
- Current bottleneck appears to be marker / hygiene state rather than continuation tree shape.
- Based on metrics added in `a080eac0 Add runtime evidence marker metrics`.

Source:
- ChatGPT Pro review pasted by the user.

Status:
- Raw review. Not yet adopted as implementation plan.

今回は GitHub 上の `a080eac0` を読んでの設計相談だよ〜。ベンチ再実測はしてないけど、今の数値と実装形から見る限り、**continuation tree より marker / hygiene state の canonicalization と path filtering が次の主戦場**だと思う。

## まず結論

低リスクで最初にやるなら、私はこれを推すよ〜。

**`active_add_ids` の path-candidate index を runtime evidence runner 側だけに入れる。**
ただし、いきなり旧 scan を消さずに、しばらくは debug / metric で「旧 scan と同じ marker 列を選んだか」を比べる形がよさそう。

理由は単純で、hit 率がかなり低いからだねぇ。

| target              |  scans |  hits | hit rate |
| ------------------- | -----: | ----: | -------: |
| `nondet_20_discard` | 52,206 |   861 |  約 1.65% |
| `showcase`          | 91,682 | 2,464 |  約 2.69% |

今の `mark_request_with_active_markers` は `active_add_ids` を全部なめて、各 marker ごとに path prefix と guard 条件を見る形になっている。ここは scan 削減余地が見える箇所だよ〜。`active_add_ids` が単なる `Vec` で、request marking が全走査している形は `runtime_evidence_run.rs` 側でそのまま読める。

一方で、**scope state の full canonicalization はまだ大改造寄り**。やる価値はあるけど、最初の一手には重い。まず path candidate を減らして、次に `MarkerPlanId` / `ScopeStateId` へ進むのが安全そうだねぇ。

---

## 1. marker / hygiene state はどう表現するのがよいか

今の実装は、だいたいこの 4 本の mutable stack で hygiene state を表している。

```rust
active_frames: Vec<EvidenceActiveFrame>
active_handler_frames: Vec<EvidenceActiveHandlerFrame>
active_add_ids: Vec<EvidenceActiveAddIdMarker>
active_marker_plans: Vec<Vec<EvidenceValueMarker>>
```

この形自体は素直だけど、canonical / persistent にするなら、**「marker の Vec」ではなく「id 化された state surface」へ分けた方がいい**と思う。現在も runner state にこの 4 stack があり、`active_marker_plans` は `Vec<Vec<EvidenceValueMarker>>` になっている。

私ならこう分けるよ〜。

```rust
struct HygieneStore {
    paths: PathInterner,
    plans: MarkerPlanInterner,
    transforms: MarkerTransformCache,
    // 大改造段階なら states もここへ
    states: ScopeStateInterner,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PathId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct MarkerPlanId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ScopeStateId(u32);
```

### `PathId`

`Vec<String>` の path prefix 判定は hot path に置かない方がいい。`PathKey` をこう持つ。

```rust
struct PathKey {
    id: PathId,
    prefix_ids: SmallVec<[PathId; 4]>,
}
```

これで request path `std::control::x::y` なら、prefix ids をたどって own-path marker 候補だけ取れる。

### `MarkerPlanId`

`EvidenceValueMarker` の小さい列は canonicalize する。

```rust
struct MarkerPlan {
    markers: Box<[EvidenceValueMarker]>,
}
```

重要なのは、**guard id を含む完全な concrete marker 列で intern する**こと。
`path` と `depth` と flags だけで同一視しない方がいい。`EvidenceGuardId` は handler hygiene の観測可能なブロッカーなので、fresh id の差を潰すと危ない。

### `ScopeStateId`

これは後段でいい。入れるなら、同一性は最低でもこれ全部を含むべきだねぇ。

```rust
struct ScopeStateKey {
    frames: PersistentSeq<EvidenceActiveFrame>,
    handler_frames: PersistentSeq<EvidenceActiveHandlerFrame>,
    active_add_ids: PersistentSeq<EvidenceActiveAddIdMarker>,
    active_marker_plan: MarkerPlanId,
}
```

ただし、最初から persistent seq を入れるより、まずは今の push/pop 型 mutable state のまま、**index と plan id だけ足す**方が低リスクだと思う。

---

## 2. `active_add_id_scans` が多く hit が少ないなら index か canonicalize か

ここは **index が先** だと思う。

理由は、今の問題は「同じ state が何回も出る」以前に、**各 request で候補にならない marker を大量に見ている**可能性が高いから。scope state を canonicalize しても、request marking が `active_add_ids` 全走査のままなら、hot path はあまり変わらないよ〜。

runtime evidence runner では、`mark_request_with_active_markers` が全 active add-id を見てから path / carry / except 条件を順に落としている。

入れるなら、control VM 側の `ScopeState` にあるような構造を runtime evidence runner 側へ小さく持ち込むのがよさそう。control VM 側にはすでに `own_path_add_markers` / `foreign_path_add_markers` / count 系の index 形がある。

イメージはこれ。

```rust
struct ActiveAddIdIndex {
    all_path: Vec<usize>,
    own_by_prefix: HashMap<PathId, Vec<usize>>,
    foreign_all: Vec<usize>,
    foreign_excluded_by_prefix: HashMap<PathId, Vec<usize>>,
}
```

request ごとに候補 index を作る。

```text
candidates =
  all_path
  + own_by_prefix[prefix in request.prefixes]
  + foreign_all - foreign_excluded_by_prefix[prefix in request.prefixes]
```

ただし注意点がある。

**候補 marker の順序は旧 scan と同じにする。**
`request.guard_ids` と `carried_guards` の順序が後続判定へ効きうるので、候補 index は最後に `sort_unstable` + `dedup` して、元の push 順で処理するのが安全だねぇ。

あと、hit 率だけでは「path mismatch が多い」のか「entry-except / already-carried で落ちている」のかは分からない。だから index 実装と同時に、最低限これを足すといいよ〜。

```text
active_add_id_path_candidates
active_add_id_path_rejects
active_add_id_entry_except_rejects
active_add_id_already_carried_rejects
active_add_id_hits
```

さらに、control VM 側の `ScopeState` は add marker push 時に `entry_except` を作って保持している。runtime evidence runner でも `entry_frame_len` だけでなく、entry 時点の guard set / compact bitset を持つと、`request_excepted_at_marker_entry` の active frame 探索を減らせる。control VM 側の `push_add_marker` は `entry_except` を作って `ScopeAddMarker` に入れている。

---

## 3. function call marker plan 変換は `plan id / scope id` で memoize してよいか

**よい。まずは `plan id` key が安全。**

今の `apply_scoped_value_result` は、`active_marker_plans.last()` を取り、毎回 `markers_for_function_call(active_markers)` を呼んでいる。そこで `function_call_marker_plans`, `inputs`, `outputs` が増えている。

`markers_for_function_call` 自体はかなり純粋な変換だよ〜。`AddId.depth` を `saturating_sub(1)` して dedupe するだけの形になっている。

だから cache key はこうで十分。

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum MarkerTransformKind {
    FunctionCall,
    ContinuationCall,
    ContinuationResume,
}

HashMap<(MarkerTransformKind, MarkerPlanId), MarkerPlanId>
```

### 安全条件

これは強めに守った方がいい。

1. **`MarkerPlanId` は concrete guard id を含む完全な marker 列を表す**

   * `GuardId` を無視した shape cache は危ない。
   * function adapter hygiene は fresh guard id を作るので、同じ source hygiene shape でも同じ plan とは限らない。

2. **marker 列の順序を保存する**

   * `combined_markers` / `dedupe_markers` は first occurrence を残す形なので、HashSet 的な無順序化は避ける。現実装も `combined_markers` は順序を保って dedupe している。

3. **memoize するのは “marker plan transform” だけ**

   * `apply_scoped_value_result` 全体を cache しない。
   * callee が `Marked` か、primitive / constructor / effect op / continuation か、closure かで、frame を張る位置が変わる。分岐は value shape 依存だよ〜。

4. **`scope id` key は後で**

   * `ScopeStateId` が active marker plan と guard identity まで完全に含むなら使っていい。
   * でもまずは `MarkerPlanId` の方が事故りにくい。

ユーザー側で「単純な function-call transform cache」は試して戻したとのことだから、同じ Vec-key cache をもう一回やる必要は薄いと思う。やるなら **Vec を key にしない plan-id 化** か、**active plan stack 自体を `MarkerPlanId` 化** する段階だねぇ。

---

## 4. 値への marker 付与をさらに遅延・削減する安全境界

方向性はかなり合っていると思う。

現実装もすでに、runtime value に marker が必要かをかなり絞っている。`runtime_value_needs_hygiene_mark` は closure / recursive closure / effect op / continuation / thunk / function adapter を true にし、pure scalar や構造値そのものは false にしている。partial constructor / primitive は中の args に marker 必要値があると true だねぇ。

さらに遅延するなら、境界はこう切るのが安全。

### marker を必ず効かせる境界

```text
apply function
force thunk
perform effect op / build request
call continuation
resume continuation
function adapter arg / body / return
project field / list item / tuple item / pattern payload
fallback-to-VM bridge
```

つまり、**pure data を見るだけなら marker は観測されない**。
でも、data の中から closure / thunk / continuation / effect op が出てきて、それが apply / force / resume / perform される瞬間には marker が必要。

### 安全な遅延表現

今の `Marked { value, markers: Vec<_> }` をより id 化して、こうする。

```rust
RuntimeEvidenceValue::Marked {
    value: SharedValue,
    plan: MarkerPlanId,
}
```

さらに進めるなら、各 value に cheap な bit を持たせる。

```rust
struct RuntimeObject {
    value: RuntimeEvidenceValue,
    may_need_hygiene_mark: bool,
}
```

これがあると、`mark_runtime_value_for_type` でも「type 的には関数を含みうるが、実値は pure data だけ」というケースを skip しやすい。今の `mark_runtime_value_for_type` は type を見て wrap するので、実値 pure でも型が higher-order なら wrapper allocation が出る余地がある。

### 危ない省略

これは避けた方がいい。

```text
record/list/tuple/data constructor の marker を単に捨てる
```

pure data ならいいけど、内部に closure / thunk / continuation が入っていると、後で field select / pattern bind された値が hygiene を失う。今の `record_fields` は `Marked` record を開いたとき、各 field value に marker を再付与する形になっている。こういう “projection 時 propagation” は残す必要がある。

---

## 5. Koka / evidence passing に寄せるなら marker state はどの層に持つか

**handler evidence object の routing layer** に持つのが自然だと思う。
value layer でも request layer でもなく、**evidence env / evidence adapter / resumption evidence** の層だねぇ。

設計メモでも、現在の marker frame / add-id / guard / carried guard は、handler-passing runtime では routing wrapper になる、という方向が書かれている。

層に分けるならこう。

```text
EvidenceEnv
  positive slots:
    op family -> handler evidence

HandlerEvidence
  handler identity
  operation family
  handler body
  outer evidence

RoutingPolicy
  guard own path
  guard foreign path
  preserve own on resume
  carry after frame
  forward/yield rule

EvidenceAdapter
  body evidence transform
  arg evidence transform
  return evidence transform

ResumptionEvidence
  continuation snapshot
  evidence env at perform
  resume routing policy

FallbackBridge
  evidence surface -> current marker/request VM representation
```

大事なのは、**callback hygiene を late marker patch として扱わない**こと。
function / thunk / continuation が evidence env を持ち、adapter が evidence env を変換し、operation は evidence slot に直接投げる。そこで扱えない領域だけ current VM fallback へ橋渡しするのがきれいだと思う。

設計メモ側でも、handler-passing path は current active marker stack を中心抽象にしない、fallback できるように別 runtime strategy として置く、という方針になっている。

---

## 6. 次に実装する一手

## 低リスクな一手: runtime evidence runner 内の add-id path candidate index

これは control VM に触らず、専用ベンチ分岐にもならない。

### 実装単位

```rust
RuntimeEvidenceRunner {
    ...
    path_interner: EvidencePathInterner,
    active_add_id_index: ActiveAddIdIndex,
}
```

`push_marker_frame` で `active_add_ids` に push するとき、同時に index にも push。`pop_marker_frame` で LIFO に pop。今の push/pop は marker frame entry で長さ snapshot を取って truncate しているので、この構造に乗せやすい。

### rollout

1. `active_add_id_candidates` / reject breakdown を足す
2. index で候補列を作る
3. debug build だけ旧 full scan と候補列の結果を比較
4. release で旧 scan を消す
5. bench で見る指標はこれ

```text
active_add_id_scans         下がる
active_add_id_candidates    新設、旧 scans より小さい
active_add_id_hits          変わらない
stdout / roots              変わらない
runtime_evidence_execute    変化を見る
```

ここで wall time が動かなければ、scan 自体は支配的でなかったと分かる。
でも、その情報自体が次の canonical state 設計に効くよ〜。

## もう一つの低〜中リスク: `MarkerPlanId` 化

add-id index の次にやるならこれ。

```rust
active_marker_plans: Vec<MarkerPlanId>
marked value markers: MarkerPlanId
continuation marker frame markers: MarkerPlanId
adapter ret_markers: MarkerPlanId
```

ただし一気に全部やらず、最初は `active_marker_plans` と `markers_for_function_call` cache だけでいい。
今の `push_active_marker_plan` は Vec equality で last dedupe して、push 時にも Vec を持つ。

## 大改造な一手: evidence env / routing policy を明示した別 runner

これは handler-passing の本命寄り。

```rust
EvidenceFunction {
    value_params,
    evidence_params,
    body,
}

EvidenceExpr {
    Perform { family, payload, evidence_slot },
    Handle { family, body, handler_evidence, parent_evidence },
    Call { callee, arg, evidence_args },
    MakeThunk { body, evidence_env },
    ForceThunk { thunk, evidence_args },
    FallbackToVm { reason, bridge },
}
```

ここでは marker state は `RuntimeEvidenceValue::Marked` や active global stack ではなく、`EvidenceEnv` と `RoutingPolicy` に入る。
`FallbackToVm` の bridge だけが current marker/request representation を作る。

これは速くなる可能性が大きいけど、今やると設計面の変更量が大きい。設計メモでも、typed hidden stack evidence を control VM shape から復元するだけでは足りず、specialize 側から runtime evidence surface を出す必要がある、という整理になっている。

---

## 私の推し順

1. **add-id path candidate index + reject breakdown**
2. **`MarkerPlanId` と transform cache**
3. **value の `may_need_hygiene_mark` bit**
4. **`ScopeStateId` / persistent state**
5. **Evidence IR dump**
6. **handler-passing runner + VM fallback bridge**

今すぐ一個だけなら、**1 を推す**よ〜。
`active_add_id_scans` の hit 率が 2% 前後なのは、かなり素直な赤ランプだねぇ。しかも control VM を触らず、handler hygiene を保ったまま、旧 scan との differential check で安全に入れられる。
