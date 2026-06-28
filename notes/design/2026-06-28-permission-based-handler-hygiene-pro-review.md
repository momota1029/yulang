うん、これはかなり良い方向だと思う。
ただし結論は少し条件付きで、**「handler 色集合」だけだと足りない。handler 色を “capability / prompt token” として、型由来の contract と scope を持たせるなら、許可制で同等に表現できる**と思うよ〜。

今の `EvidenceSignalHygiene` は `guard_ids / carried_guards / handler_boundary` をまとめて、`EvidenceRequest` と `EvidenceDirectTailResumptive` の両方に載る形になっている。つまり request からは分離したけど、意味論はまだ「後から guard で handler を避ける」方式だねぇ。

## まず結論

**許可制へ移す価値はある。**
特に Evidence VM / Koka 的 evidence passing / native lowering を考えるなら、拒否制より自然だと思う。

ただし、許可制の正体はこうじゃないと危ない。

```text
handler color = 単なる色ではなく、handler capability / prompt token

effect allowed set =
  「この effect occurrence を捕捉してよい handler capability の集合」
  ただし family / contract / scope / generation を含む
```

つまり handler はこう見る。

```text
can_handle(handler, effect):
  family_matches(handler.family, effect.family)
  && handler.capability ∈ effect.allowed_caps
  && capability_scope_is_live(handler.capability)
  && operation_mode_matches(handler, effect)
```

これなら「内側 handler がたまたま path 一致したから捕捉する」を防げる。逆に、allowed set がただの `HashSet<HandlerColor>` で、scope や contract から切り離されているなら危ないねぇ。

---

## 1. 許可制で Yulang の handler hygiene は同等に表現できるか

**表現できると思う。**
ただし「拒否リストの補集合」ではなく、**型推論が許可した捕捉 capability だけを effect occurrence に付ける**形にする必要がある。

今の方式は、effect が発生したあとに active add-id marker を走査して `guard_ids / carried_guards` を hygiene payload に足し、catch 側で `visible_operation_resumptive_parts` が guard を見て捕捉可否を決めている。

許可制では、その判定をこう置き換える。

```rust
struct EffectOccurrenceEvidence {
    family: PathId,
    allowed_handlers: HandlerAllowedSetId,
    provenance: EffectProvenanceId,
}

struct HandlerCapability {
    id: HandlerCapId,
    family: PathId,
    scope: HandlerScopeId,
    contract: EffectContractId,
    mode: HandlerMode,
}
```

現在の判定:

```text
handler が path に一致する
ただし guard / carried guard / boundary が block しない場合だけ捕捉
```

許可制の判定:

```text
handler が path に一致する
かつ handler.cap ∈ effect.allowed_handlers の場合だけ捕捉
```

この二つが同値になるように lowering できればいい。

ただし注意点はある。現在の `carried_guards` は「resume された先でどの handler alias を露出してよいか」まで持っている。`carried_exposed_guard_ids_at_marker_entry` は `preserve_own_on_resume` や外側 matching handler を見て exposed guard を作っている。 だから許可制でも、単なる allowed set だけではなく、**resume 時に allowed set をどう復元・制限するか**が必要になる。

なので同等性の対応はこうだねぇ。

| 現行                             | 許可制                                        |
| ------------------------------ | ------------------------------------------ |
| `GuardId`                      | `HandlerCapId`                             |
| `AddId marker`                 | allowed set transform                      |
| `carried_guards`               | resume allowed-set delta / exposed caps    |
| `handler_boundary`             | boundary-local allowed-set mask            |
| `request_guard_for_path_parts` | `handler.cap ∈ allowed_set`                |
| marker close                   | allowed-set close / capability propagation |

---

## 2. callback 由来 effect を偶然捕捉しない性質は allowed set だけで守れるか

**allowed set の伝播だけで守れる。ただし “どこで allowed set を作るか” が本体。**

雑に「現在見えている handler cap を全部 effect に入れる」だと壊れる。callback 境界では、呼び出し元由来の effect に対して、内側 handler cap を勝手に足してはいけない。

Yulang の型理論ドキュメントでも、compose みたいな高階関数では `g x` の `last` を `f` の中の handler が捕捉してはいけない、これを handler hygiene と呼ぶ、と整理されている。 また、明示 annotation がない高階 callback 境界では新しい capture contract を与えず、callback-origin effect は empty visibility evidence で保護されうる、とある。

許可制ではこうする。

```text
callback / function argument boundary:
  explicit contract なし:
    callback-origin effects.allowed = Empty

  [_] contract:
    surface row に対応する allowed caps を渡す

  [console] contract:
    console を捕捉してよい handler cap だけ渡す

  covariant result filter:
    allowed を増やさない
    逃げる effect の静的チェックだけ行う
```

つまり、callback の body で effect が起きたとき、その effect occurrence は「呼び出し先の現在 handler」ではなく、**callback value が受け取った contract-passed capability** から allowed set を作る。

```rust
struct FunctionValue {
    code: FunctionId,
    lexical_env: EnvId,

    // 作成位置の evidence
    lexical_caps: EvidenceEnvId,

    // 引数/戻り値境界で許可される capture contract
    adapter: Option<EvidenceAdapterId>,
}

struct EvidenceAdapter {
    arg_allowed_transform: AllowedSetTransformId,
    body_allowed_transform: AllowedSetTransformId,
    ret_allowed_transform: AllowedSetTransformId,
}
```

ここは既存の handler-passing 設計メモとも合う。runtime handler-passing では callback-derived effects が unrelated inner handler に捕捉されてはいけないし、明示 effect annotation が local contract として subtraction を許す、と整理されている。

---

## 3. directed stack weight / effect subtraction とどう対応づけるべきか

対応はかなり綺麗に書けると思う。

今の型推論では、solver が directed stack weights を持ち、handler はその weight を通して visible な effect family だけを subtract できる。`Common(L)` と handler family `H` の交差 `J = H ∩ Common(L)` だけが消費可能、という説明になっている。

許可制では、これをこう読む。

```text
take(H) entry
  = family H を扱う handler capability を allowed budget に追加する可能性

pop
  = scope を閉じるが、向きによって allowed budget を復元しない

Common(L)
  = その occurrence に届いている allowed handler capability の family 集合

row subtraction
  = row head の allowed_caps に現在 handler cap が入っている場合だけ消費
```

もう少し具体的にはこう。

```rust
struct TypeEffectOccurrence {
    family: EffectFamilyId,
    row_var: RowVarId,

    // solver-local, public type には出さない
    visibility: VisibilityBudgetId,
}

struct VisibilityBudget {
    allowed_caps_by_family: Map<EffectFamilyId, CapSetId>,
}
```

`catch H` が handler cap `h` を作る。

```text
catch H introduces h : HandlerCap(H)

inside body:
  visible occurrence gets allowed_caps += h
```

ただし function argument は contravariant なので、weight の向きが逆になる。型理論ドキュメントでも function arguments は contravariant なので左右の direction が swap すると書かれている。 ここを runtime surface に落とすときは、単に「現在の handler cap を全部渡す」じゃなく、**specialize 時点で occurrence ごとに許可された cap slot を焼く**のが安全だねぇ。

subtraction はこうなる。

```text
handler h catches effect e
iff
  e.family ∈ h.family
  and h.cap_id ∈ e.allowed_caps
```

`take(Empty)` はそのまま `allowed_caps = ∅`。
今の docs の `#u[Empty]` は、「この occurrence は boundary `u` では消費不可」という意味だと読める。

だから型対応はこれでよさそう。

| solver          | 許可制 runtime                                               |
| --------------- | --------------------------------------------------------- |
| `take(H)`       | handler capability を allowed budget に追加                   |
| `take(Empty)`   | allowed set empty                                         |
| `pop`           | capability scope を閉じる / outward propagation しない           |
| `Common(L)`     | occurrence が持つ allowed capability set                     |
| row subtraction | `handler_cap ∈ allowed_set` のときだけ消費                       |
| residual row    | allowed set から消費済み cap を除いた、または別 occurrence として再包装された row |

---

## 4. public type から private evidence を隠す設計と矛盾しないか

**矛盾しない。**
むしろ許可制の方が隠しやすい。

public type に出すのは effect family と row variable だけ。`HandlerCapId` / `AllowedSetId` / `VisibilityBudgetId` は solver-local / lowering-local / cache sidecar に置く。

docs でも、stack ids と pop counts は inference evidence であって source-level type syntax ではなく、通常の API documentation は value types と effect rows として読む、と整理されている。

必要なら compiler-oriented dump だけ出す。

```text
public:
  (a -> [gamma] b) -> ...

internal dump:
  gamma @ allowed={cap_u?}
  gamma#u[Empty]
```

注意点は cross-unit / cache だねぇ。handler-passing メモでも、runtime evidence surface は `specialize` 中の weighted type graph がまだある段階で出す必要があり、mono/control IR から復元しようとすると solver-local stack relation を落とす、と書かれている。

だから public type から隠してよいけど、**compiler artifact からは消しちゃだめ**。

```text
source public type:
  hide caps

runtime evidence sidecar:
  keep caps / allowed sets / slot ids

generic fallback:
  allowed set -> marker/guard bridge を持つ
```

---

## 5. Evidence VM では handler color / allowed set をどの IR に置くのが自然か

置き場所は 3 層に分けるのが自然だと思う。

### Handler color は `EvidenceVmHandlerObjectPlan`

今の handler object plan はすでに `id / handler / slot_id / path / arm_body / arm_class / continuation_use / definition_env` を持っている。ここへ `capability_id` を入れるのが一番自然。

```rust
struct EvidenceVmHandlerObjectPlan {
    id: u32,
    capability_id: HandlerCapId,
    handler: ExprId,
    slot_id: u32,
    path: Vec<String>,
    arm_body: ExprId,
    arm_class: EvidenceVmHandlerArmClass,
    continuation_use: EvidenceVmContinuationUsePlan,
    definition_env: Vec<u32>,
}
```

### allowed set は `EvidenceVmOperationObjectPlan` と `EvidenceVmSlotKey`

今の operation plan は `slot: EvidenceVmSlotKey` を持ち、slot key は `family + route` だけになっている。route は `Positive / Blocked / UnknownFallback` の 3 種類だねぇ。

許可制へ進めるなら、ここを濃くする。

```rust
struct EvidenceVmSlotKey {
    family: PathId,
    route: EvidenceVmSlotRouteKey,

    // new
    visibility: VisibilityBudgetId,
    contract: EffectContractId,
}
```

または slot key を太らせすぎず、operation object に載せる。

```rust
struct EvidenceVmOperationObjectPlan {
    expr: ExprId,
    slot_id: u32,
    candidate_handler: Option<u32>,
    execution: EvidenceVmOperationExecutionPlan,

    // new
    allowed_handlers: AllowedHandlerSetId,
}
```

私なら最初は **operation object 側**に置くかなぁ。理由は、同じ family/route slot でも occurrence ごとに callback boundary 由来の allowed set が違う可能性があるから。

### runtime signal には `AllowedSetId` だけ載せる

現行の `EvidenceSignalHygiene` をいきなり消さず、次の形を足す。

```rust
enum EvidenceSignalVisibility {
    GuardHygiene(EvidenceSignalHygiene),
    AllowedCaps {
        family: PathId,
        allowed: AllowedHandlerSetId,
        fallback_hygiene: Option<EvidenceSignalHygiene>,
    },
}
```

最終形では `EvidenceSignalHygiene` は fallback bridge 側に落とせる。

---

## 6. Koka 的 evidence passing / native lowering へ進むなら、許可制へ移す価値はあるか

**ある。かなりある。**

理由は単純で、Koka 的 evidence passing は基本的に positive routing だから。operation が evidence slot を見て handler object を直接呼ぶ。Yulang 側でも、handler-passing runtime は dynamic handler stack search ではなく evidence object call へ寄せる方針になっている。

拒否制のままだと、direct call でも毎回こういう問いが残る。

```text
この handler に飛んでよい？
いや、拒否色を見ないと分からない
carried guard は？
handler boundary は？
resume 先では？
```

許可制なら、operation 側が最初から「飛んでよい handler cap」を持つ。

```text
perform:
  cap = allowed.resolve_nearest(family)
  cap.call(payload, resume)
```

これで request-free route の不変条件が軽くなる。

```text
current request-free:
  handler pointer + negative evidence が必要

permission request-free:
  allowed handler cap があれば direct
  なければ forward/fallback
```

既存メモでも、Koka 的には positive routing が主役だが、Yulang では contracted visibility / callback blocker / provider grant provenance / resume policy が追加で必要、と整理されている。

つまり、許可制にしても hygiene が消えるわけじゃない。
でも **negative evidence を hot path から “allowed cap を作る時点” へ移せる**。これは native lowering ではかなり効くと思うよ〜。

---

## 7. 既存 marker/guard/request fallback と段階的に互換させる移行案

ある。いきなり置換しない方がいい。

### Phase 0: 同値チェッカーだけ入れる

現行の `EvidenceSignalHygiene` は残す。
新しく `AllowedSet` を sidecar 的に作る。

```rust
struct EvidenceSignalHygiene {
    guard_ids: Vec<EvidenceGuardId>,
    carried_guards: Vec<EvidenceCarriedGuard>,
    handler_boundary: Option<EvidenceHandlerBoundary>,

    // debug / staged
    allowed_caps: Option<AllowedHandlerSetId>,
}
```

catch 可視性判定で、debug build だけ比較する。

```rust
old_visible =
  visible_operation_resumptive_parts(...guard_ids, carried_guards...)

new_visible =
  allowed_caps.contains(handler.capability)

debug_assert_eq!(old_visible, new_visible)
```

現行 catch 側は `visible_operation_resumptive` が request hygiene を見て、direct-tail も同じ `visible_operation_resumptive_parts` を使っている。ここに比較を差し込める。

### Phase 1: handler capability id を導入

`EvidenceVmHandlerObjectPlan` に `capability_id` を足す。
まだ実行には使わない。dump と debug check だけ。

```rust
struct HandlerCapability {
    id: HandlerCapId,
    handler_object_id: u32,
    family: PathId,
    scope: HandlerScopeId,
}
```

### Phase 2: operation occurrence に allowed set を持たせる

`EvidenceVmOperationObjectPlan` に `allowed_handlers` を足す。

```rust
struct EvidenceVmOperationObjectPlan {
    ...
    allowed_handlers: AllowedHandlerSetId,
}
```

この allowed set は `specialize` の runtime evidence surface から来るべき。control IR だけから復元しない方がいい。

### Phase 3: fallback bridge を作る

許可制 signal から現行 request/guard へ戻す橋を作る。

```rust
struct AllowedToMarkerBridge {
    allowed: AllowedHandlerSetId,
    family: PathId,

    // fallback 用に旧 hygiene を再構成、または旧 hygiene を併走保持
    fn to_signal_hygiene(...) -> EvidenceSignalHygiene
}
```

最初は旧 hygiene を併走保持していい。

```rust
struct EvidenceSignalVisibility {
    allowed: AllowedHandlerSetId,
    legacy: EvidenceSignalHygiene,
}
```

### Phase 4: request-free direct route だけ allowed set を使う

generic request fallback は旧方式のまま。
DirectAbortive / DirectTailResumptive だけ allowed set を使う。

```text
if handler.cap ∈ allowed:
  Direct*
else:
  GenericRequest with legacy hygiene
```

この段階なら regression が出ても fallback へ戻せる。

### Phase 5: marker close を allowed-set close へ置き換える

`EvidenceCallBoundary::close` の中身を、marker close から allowed-set transform へ少しずつ移す。

既存メモでも、`apply_scoped_value_result` は call boundary を open して結果を close する意味論 primitive として扱うべき、と整理されている。 さらに request-free fast path は request を消すのではなく、request が持っていた hygiene 観測を signal / grant / resumption 側へ移す最適化だとまとめられている。

許可制でもここは同じ。

```text
CallBoundary::close(result):
  Value:
    object graph の allowed evidence を close

  DirectTail:
    payload allowed を close
    continuation resume allowed を attach

  Yield:
    allowed set + continuation fragments を保存

  FallbackRequest:
    allowed -> legacy hygiene bridge
```

---

## 私のおすすめ設計

一気に「allowed set だけ」にしないで、こういう名前にするのが良さそう。

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct HandlerCapId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct AllowedSetId(u32);

struct HandlerCapability {
    id: HandlerCapId,
    family: PathId,
    handler_object: HandlerObjectId,
    scope: HandlerScopeId,
    contract: EffectContractId,
}

struct AllowedHandlerSet {
    // small set or interned bitset
    caps: SmallVec<[HandlerCapId; 2]>,

    // fallback/debug
    provenance: VisibilityProvenanceId,
}

struct EvidenceOperationVisibility {
    family: PathId,
    allowed: AllowedSetId,

    // 移行中だけ
    legacy_hygiene: Option<EvidenceSignalHygiene>,
}
```

そして capture 判定はこう。

```rust
fn can_capture(handler: HandlerCapability, op: EvidenceOperationVisibility) -> bool {
    path_matches(handler.family, op.family)
        && allowed_set(op.allowed).contains(handler.id)
}
```

ただし provider-env route ではさらに gate が必要。

```rust
fn can_capture_provider(handler, op, grant) -> bool {
    can_capture(handler, op)
        && provider_grant_gate_passes(grant)
}
```

現行コードでは provider grant は `scope_id + hygiene_baseline` を `EvidenceProviderGrantGate` として取り出す形まで来ているから、この gate を allowed capability の scope check に寄せられる。

---

## 最終判断

**許可制は採用候補として強い。**
ただし、「拒否リストを allowed set に機械変換する」だけだと、negative evidence の場所が変わるだけで大して軽くならない。

価値が出る形はこれ。

```text
型推論:
  directed stack weight から occurrence ごとの allowed capability を作る

specialize/runtime evidence surface:
  allowed set / handler cap / contract を sidecar に残す

Evidence VM:
  request-free direct route は allowed cap で判定
  fallback は allowed -> marker/guard bridge で現 VM に戻す

native lowering:
  cap が単一なら direct call
  cap が empty なら fallback/forward
  cap が複数なら small dispatch
```

一言で言うと、**拒否制は VM の防御機構としては強いけど、evidence passing の primary semantics には重い。許可制を primary にして、既存 marker/guard を fallback bridge に下げる**のが一番きれいだと思うよ〜。
